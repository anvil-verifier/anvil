use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    api_server::{types::*, state_machine::*},
    cluster::*, 
    message::*
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::{
    trusted::{spec_types::*, step::*, util::*, liveness_theorem::*, rely_guarantee::*},
    model::{install::*, reconciler::*},
    proof::{predicate::*, liveness::api_actions::*, helper_lemmas::*, helper_invariants},
    proof::liveness::rolling_update::predicate::*,
    proof::liveness::rolling_update::composition::*,
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use crate::reconciler::spec::io::*;
use crate::vstd_ext::{seq_lib::*, set_lib::*};
use vstd::{seq_lib::*, map_lib::*, multiset::*};
use vstd::prelude::*;

verus !{

// ===== Top-level lemma =====
// Entry point called from ranking_decreases_after_vrs_esr in composition.rs.
//
// Proves: Init ∧ no_pending ~> ¬(conjuncted_desired_state_is ∧ identity)
//
// Proof chain:
//   Init ~> send_list_req ~> receive_list_resp (with status info) 
//     ~> send_scale_new_vrs_by_one_req ~> API processes req
//     ~> etcd VRS spec.replicas changed ~> ¬desired_state_is(new_vrs)

pub proof fn lemma_from_init_to_not_desired_state_is(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster,
    controller_id: int, vrs_set: Set<VReplicaSetView>, n: nat
)
    requires
        n > 0,
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
        spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
        spec.entails(always(lift_state(inductive_current_state_matches(vd, controller_id)))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
        spec.entails(tla_forall((|i| cluster.external_next().weak_fairness((controller_id, i))))),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        // □ q(n) ∧ □ identity(n)
        spec.entails(always(lift_state(conjuncted_current_state_matches_vrs_with_replica_diff(vrs_set, vd, n)))),
        spec.entails(always(lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)))),
    ensures
        spec.entails(
            lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![Init]),
                no_pending_req_in_cluster(vd, controller_id)
            )).leads_to(not(
                lift_state(conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, n))
                    .and(lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)))
            ))
        ),
{
    assume(false); // skeleton
}

// ===== Step 1: Init ~> send_list_req =====

pub proof fn lemma_from_init_step_to_send_list_vrs_req(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
    requires
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    ensures
        spec.entails(lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![Init]),
                no_pending_req_in_cluster(vd, controller_id)
            ))
            .leads_to(lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
                pending_list_req_in_flight(vd, controller_id)
            )))),
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Init]),
        no_pending_req_in_cluster(vd, controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        pending_list_req_in_flight(vd, controller_id)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
    );
    let input = (None::<Message>, Some(vd.object_ref()));
    assert(forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) ==> pre(s_prime) || post(s_prime));
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

// ===== Step 2: send_list_req ~> receive_list_resp =====

pub proof fn lemma_from_after_send_list_vrs_req_to_receive_list_vrs_resp(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster,
    controller_id: int, req_msg: Message, vrs_set: Set<VReplicaSetView>, n: nat
)
    requires
        n > 0,
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
        spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
        spec.entails(always(lift_state(inductive_current_state_matches(vd, controller_id)))),
        spec.entails(always(lift_state(conjuncted_current_state_matches_vrs_with_replica_diff(vrs_set, vd, n)))),
        spec.entails(always(lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)))),
    ensures
        spec.entails(lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
                req_msg_is_pending_list_req_in_flight(vd, controller_id, req_msg)
            ))
            .leads_to(lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
                ru_exists_pending_list_resp_in_flight_and_match_req(vd, controller_id)
            )))),
{
    let inv = lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id));
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        req_msg_is_pending_list_req_in_flight(vd, controller_id, req_msg)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        ru_exists_pending_list_resp_in_flight_and_match_req(vd, controller_id)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& conjuncted_current_state_matches_vrs_with_replica_diff(vrs_set, vd, n)(s)
        &&& current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)(s)
        &&& inductive_current_state_matches(vd, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
        lift_state(conjuncted_current_state_matches_vrs_with_replica_diff(vrs_set, vd, n)),
        lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)),
        lift_state(inductive_current_state_matches(vd, controller_id))
    );
    let input = Some(req_msg);
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                if msg == req_msg {
                    let resp_msg = lemma_list_vrs_request_returns_ok_with_objs_matching_vd(
                        s, s_prime, vd, cluster, controller_id, msg
                    );
                    assert(resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s_prime));
                    assume(ru_resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s_prime));
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& ru_resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s_prime)
                    });
                }
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let msg = input->0;
        let resp_msg = lemma_list_vrs_request_returns_ok_with_objs_matching_vd(
            s, s_prime, vd, cluster, controller_id, msg,
        );
        assert(resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s_prime));
        assume(ru_resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s_prime));
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& ru_resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s_prime)
        });
    }
    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

// ===== Step 3: receive_list_resp ~> send_scale_new_vrs_by_one_req =====
// Since n > 0, the new VRS has spec.replicas != vd.spec.replicas,
// so mismatch_replicas is true → the controller calls scale_new_vrs.

pub proof fn lemma_from_after_receive_list_vrs_resp_to_send_scale_new_vrs_by_one_req(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster,
    controller_id: int, resp_msg: Message, nv_uid_key: (Uid, ObjectRef),
    vrs_set: Set<VReplicaSetView>, n: nat
)
    requires
        n > 0,
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
        spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
        spec.entails(always(lift_state(inductive_current_state_matches(vd, controller_id)))),
        spec.entails(always(lift_state(conjuncted_current_state_matches_vrs_with_replica_diff(vrs_set, vd, n)))),
        spec.entails(always(lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)))),
    ensures
        spec.entails(lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
                ru_resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
                ru_resp_objs_with_new_vrs_status_matching_replicas_and_no_old_vrs(vd, controller_id, resp_msg, Some(nv_uid_key)),
                ru_etcd_state_is(vd, controller_id, nv_uid_key)
            ))
            .leads_to(lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
                ru_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id, nv_uid_key),
                ru_etcd_state_is(vd, controller_id, nv_uid_key),
                ru_local_state_is(vd, controller_id, nv_uid_key),
                ru_local_state_is_valid_and_coherent_with_etcd(vd, controller_id)
            )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        ru_resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
        ru_resp_objs_with_new_vrs_status_matching_replicas_and_no_old_vrs(vd, controller_id, resp_msg, Some(nv_uid_key)),
        ru_etcd_state_is(vd, controller_id, nv_uid_key)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        ru_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id, nv_uid_key),
        ru_etcd_state_is(vd, controller_id, nv_uid_key),
        ru_local_state_is(vd, controller_id, nv_uid_key),
        ru_local_state_is_valid_and_coherent_with_etcd(vd, controller_id)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
    );
    let input = (Some(resp_msg), Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                assume(pre(s_prime) || post(s_prime));
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == Some(resp_msg) && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    VReplicaSetView::marshal_preserves_integrity();
                    // mismatch_replicas is true because:
                    //   new_vrs.status->0.replicas == new_vrs.spec.replicas (from status matching)
                    //   new_vrs.spec.replicas != vd.spec.replicas (from ru_etcd_state_is: != )
                    //   So status.replicas != vd.spec.replicas → mismatch_replicas is TRUE
                    // → scale_new_vrs called → produces GetThenUpdate req
                    assume(post(s_prime));
                }
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        VDeploymentReconcileState::marshal_preserves_integrity();
        VReplicaSetView::marshal_preserves_integrity();
        assume(post(s_prime));
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

// ===== Step 4: send_scale_new_vrs_by_one_req ~> ¬desired_state_is =====
// After the GetThenUpdate request is processed by the API server, the etcd VRS has
// spec.replicas changed by ±1. Since the VRS identity in vrs_set has the OLD spec.replicas,
// desired_state_is(vrs) becomes false.

pub proof fn lemma_from_after_send_scale_new_vrs_by_one_req_to_not_desired_state_is(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster,
    controller_id: int, req_msg: Message, nv_uid_key: (Uid, ObjectRef),
    vrs_set: Set<VReplicaSetView>, n: nat
)
    requires
        n > 0,
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
        spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
        spec.entails(always(lift_state(inductive_current_state_matches(vd, controller_id)))),
        spec.entails(always(lift_state(conjuncted_current_state_matches_vrs_with_replica_diff(vrs_set, vd, n)))),
        spec.entails(always(lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)))),
    ensures
        spec.entails(lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
                ru_req_msg_is_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id, req_msg, nv_uid_key),
                ru_etcd_state_is(vd, controller_id, nv_uid_key),
                ru_local_state_is(vd, controller_id, nv_uid_key),
                ru_local_state_is_valid_and_coherent_with_etcd(vd, controller_id)
            ))
            .leads_to(not(
                lift_state(conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, n))
                    .and(lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)))
            ))),
{
    assume(false); // skeleton
    // Proof outline:
    // 1. API server processes GetThenUpdate → etcd VRS spec.replicas changes by ±1
    //    (guaranteed by WF of api_server_next)
    // 2. After update, etcd VRS spec.replicas != old spec.replicas (it changed by ±1)
    // 3. The VRS identity in vrs_set has the OLD spec.replicas
    //    desired_state_is(vrs) requires etcd[key].spec == vrs.spec
    //    But etcd spec.replicas changed → desired_state_is(vrs) is false
    // 4. Therefore ¬(conjuncted_desired_state_is ∧ identity)
    //
    // Note: after the scale, ru_etcd_state_is may or may not hold (if n==1, new replicas
    // might equal vd.spec.replicas), but we don't need it — we directly prove ¬desired_state_is.
}

}