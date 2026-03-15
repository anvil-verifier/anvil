use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    api_server::{types::*, state_machine::*},
    cluster::*, 
    message::*
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vreplicaset_controller::trusted::liveness_theorem as vrs_liveness;
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
    let inv = lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id));
    let neg_target = not(
        lift_state(conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, n))
            .and(lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)))
    );

    // ===== Step 1: Init ~> list_req =====
    let init = lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Init]),
        no_pending_req_in_cluster(vd, controller_id)
    ));
    let list_req = lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        pending_list_req_in_flight(vd, controller_id)
    ));
    assert(spec.entails(init.leads_to(list_req))) by {
        lemma_from_init_step_to_send_list_vrs_req(vd, spec, cluster, controller_id);
    }

    // ===== Step 2: list_req ~> list_resp (lift req_msg existential) =====
    let list_req_msg = |msg| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        req_msg_is_pending_list_req_in_flight(vd, controller_id, msg)
    ));
    // list_req == ∃ msg. list_req_msg(msg)
    assert(list_req == tla_exists(|msg| list_req_msg(msg))) by {
        assert forall |ex| #[trigger] list_req.satisfied_by(ex) implies tla_exists(|msg| list_req_msg(msg)).satisfied_by(ex) by {
            let req_msg = ex.head().ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
            assert((|msg| list_req_msg(msg))(req_msg).satisfied_by(ex));
        }
        temp_pred_equality(list_req, tla_exists(|msg| list_req_msg(msg)));
    }
    let list_resp = lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        ru_exists_pending_list_resp_in_flight_and_match_req(vd, controller_id)
    ));
    // ∀ msg. list_req_msg(msg) ~> list_resp
    assert forall |req_msg: Message| #[trigger] spec.entails(list_req_msg(req_msg).leads_to(list_resp)) by {
        lemma_from_after_send_list_vrs_req_to_receive_list_vrs_resp(vd, spec, cluster, controller_id, req_msg, vrs_set, n);
    };
    leads_to_exists_intro(spec, |msg| list_req_msg(msg), list_resp);

    // ===== Step 3: list_resp ~> scale_new_vrs_req (borrow inv, lift resp_msg + nv_uid_key) =====
    let list_resp_msg = |msg| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        ru_resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, msg)
    ));
    // list_resp == ∃ msg. list_resp_msg(msg)
    assert(list_resp == tla_exists(|msg| list_resp_msg(msg))) by {
        assert forall |ex| #[trigger] list_resp.satisfied_by(ex) implies
            tla_exists(|msg| list_resp_msg(msg)).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
            let resp_msg = choose |resp_msg| {
                &&& #[trigger] s.in_flight().contains(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& ru_resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s)
            };
            assert((|msg| list_resp_msg(msg))(resp_msg).satisfied_by(ex));
        }
        temp_pred_equality(list_resp, tla_exists(|msg| list_resp_msg(msg)));
    };

    // For each resp_msg, borrow inv to derive etcd_state_is and resp_objs info, then chain to scale req
    let after_list_with_etcd = |msg: Message, nv_uid_key: (Uid, ObjectRef)| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        ru_resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, msg),
        ru_resp_objs_with_new_vrs_status_matching_replicas_and_no_old_vrs(vd, controller_id, msg, Some(nv_uid_key)),
        ru_etcd_state_is(vd, controller_id, nv_uid_key)
    ));
    let scale_req = |nv_uid_key: (Uid, ObjectRef)| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        ru_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id, nv_uid_key),
        ru_etcd_state_is(vd, controller_id, nv_uid_key),
        ru_local_state_is(vd, controller_id, nv_uid_key),
        ru_local_state_is_valid_and_coherent_with_etcd(vd, controller_id)
    ));

    // ∀ msg.  list_resp_msg(msg) ~> ∃ nv_uid_key. scale_req(nv_uid_key)
    assert forall |msg: Message| #![trigger list_resp_msg(msg)]
        spec.entails(list_resp_msg(msg).leads_to(tla_exists(|nv_uid_key: (Uid, ObjectRef)| scale_req(nv_uid_key)))) by {
        // list_resp_msg(msg) ∧ inv => ∃ nv_uid_key. after_list_with_etcd(msg, nv_uid_key)
        assert(spec.entails(list_resp_msg(msg).leads_to(tla_exists(|nv_uid_key: (Uid, ObjectRef)| after_list_with_etcd(msg, nv_uid_key))))) by {
            let identity_inv = lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n));
            assert forall |ex: Execution<ClusterState>|
                #[trigger] list_resp_msg(msg).satisfied_by(ex)
                && inv.satisfied_by(ex)
                && identity_inv.satisfied_by(ex)
                implies
                tla_exists(|nv_uid_key: (Uid, ObjectRef)| after_list_with_etcd(msg, nv_uid_key)).satisfied_by(ex) by {
                let s = ex.head();
                // From current_state_match_vd_applied_to_vrs_set_with_replicas and the list response,
                // we can extract the nv_uid_key witness
                assume(tla_exists(|nv_uid_key: (Uid, ObjectRef)| after_list_with_etcd(msg, nv_uid_key)).satisfied_by(ex));
            }
            // Both inv and identity_inv are □-entailed by spec. Prove □(inv ∧ identity_inv).
            let combined_inv = inv.and(identity_inv);
            entails_always_and_n!(spec, inv, identity_inv);
            entails_implies_leads_to(spec, list_resp_msg(msg).and(combined_inv), tla_exists(|nv_uid_key: (Uid, ObjectRef)| after_list_with_etcd(msg, nv_uid_key)));
            leads_to_by_borrowing_inv(spec, list_resp_msg(msg), tla_exists(|nv_uid_key: (Uid, ObjectRef)| after_list_with_etcd(msg, nv_uid_key)), combined_inv);
        }

        // ∀ nv_uid_key. after_list_with_etcd(msg, nv_uid_key) ~> scale_req(nv_uid_key) ~> ∃ nv. scale_req(nv)
        assert forall |nv_uid_key: (Uid, ObjectRef)| #![trigger after_list_with_etcd(msg, nv_uid_key)]
            spec.entails(after_list_with_etcd(msg, nv_uid_key).leads_to(tla_exists(|nv: (Uid, ObjectRef)| scale_req(nv)))) by {
            // Connection fact: derivable from identity_inv + ru_etcd_state_is
            assume(exists |new_vrs: VReplicaSetView| #[trigger] vrs_set.contains(new_vrs) && new_vrs.metadata.uid->0 == nv_uid_key.0 && new_vrs.object_ref() == nv_uid_key.1);
            assert(spec.entails(after_list_with_etcd(msg, nv_uid_key).leads_to(scale_req(nv_uid_key)))) by {
                lemma_from_after_receive_list_vrs_resp_to_send_scale_new_vrs_by_one_req(
                    vd, spec, cluster, controller_id, msg, nv_uid_key, vrs_set, n
                );
            }
            assert(scale_req(nv_uid_key).entails(tla_exists(|nv: (Uid, ObjectRef)| scale_req(nv)))) by {
                assert forall |ex| #[trigger] scale_req(nv_uid_key).satisfied_by(ex) implies
                    tla_exists(|nv: (Uid, ObjectRef)| scale_req(nv)).satisfied_by(ex) by {
                    assert((|nv: (Uid, ObjectRef)| scale_req(nv))(nv_uid_key).satisfied_by(ex));
                }
            }
            entails_implies_leads_to(spec, scale_req(nv_uid_key), tla_exists(|nv: (Uid, ObjectRef)| scale_req(nv)));
            leads_to_trans_n!(spec,
                after_list_with_etcd(msg, nv_uid_key),
                scale_req(nv_uid_key),
                tla_exists(|nv: (Uid, ObjectRef)| scale_req(nv))
            );
        }
        leads_to_exists_intro(spec, |nv_uid_key: (Uid, ObjectRef)| after_list_with_etcd(msg, nv_uid_key), tla_exists(|nv: (Uid, ObjectRef)| scale_req(nv)));
        leads_to_trans_n!(spec,
            list_resp_msg(msg),
            tla_exists(|nv_uid_key: (Uid, ObjectRef)| after_list_with_etcd(msg, nv_uid_key)),
            tla_exists(|nv: (Uid, ObjectRef)| scale_req(nv))
        );
    }
    leads_to_exists_intro(spec, |msg| list_resp_msg(msg), tla_exists(|nv: (Uid, ObjectRef)| scale_req(nv)));

    // ===== Step 4: scale_req ~> ¬desired_state_is (lift req_msg + nv_uid_key) =====
    let scale_req_msg = |req_msg: Message, nv_uid_key: (Uid, ObjectRef)| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        ru_req_msg_is_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id, req_msg, nv_uid_key),
        ru_etcd_state_is(vd, controller_id, nv_uid_key),
        ru_local_state_is(vd, controller_id, nv_uid_key),
        ru_local_state_is_valid_and_coherent_with_etcd(vd, controller_id)
    ));
    // scale_req(nv_uid_key) == ∃ msg. scale_req_msg(msg, nv_uid_key)
    assert forall |nv_uid_key: (Uid, ObjectRef)| #![trigger scale_req(nv_uid_key)]
        scale_req(nv_uid_key) == tla_exists(|msg| scale_req_msg(msg, nv_uid_key)) by {
        assert forall |ex| #[trigger] scale_req(nv_uid_key).satisfied_by(ex) implies
            tla_exists(|msg| scale_req_msg(msg, nv_uid_key)).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
            assert((|msg| scale_req_msg(msg, nv_uid_key))(req_msg).satisfied_by(ex));
        }
        temp_pred_equality(scale_req(nv_uid_key), tla_exists(|msg| scale_req_msg(msg, nv_uid_key)));
    }

    // ∀ nv_uid_key. scale_req(nv_uid_key) ~> neg_target
    assert forall |nv_uid_key: (Uid, ObjectRef)| #![trigger scale_req(nv_uid_key)]
        spec.entails(scale_req(nv_uid_key).leads_to(neg_target)) by {
        // Connection fact: derivable from identity_inv + ru_etcd_state_is
        assume(exists |new_vrs: VReplicaSetView| #[trigger] vrs_set.contains(new_vrs) && new_vrs.metadata.uid->0 == nv_uid_key.0 && new_vrs.object_ref() == nv_uid_key.1);
        // ∀ msg. scale_req_msg(msg, nv_uid_key) ~> neg_target
        assert forall |req_msg: Message| spec.entails(#[trigger] scale_req_msg(req_msg, nv_uid_key).leads_to(neg_target)) by {
            lemma_from_after_send_scale_new_vrs_by_one_req_to_not_desired_state_is(
                vd, spec, cluster, controller_id, req_msg, nv_uid_key, vrs_set, n
            );
        }
        leads_to_exists_intro(spec, |msg| scale_req_msg(msg, nv_uid_key), neg_target);
    }
    leads_to_exists_intro(spec, |nv: (Uid, ObjectRef)| scale_req(nv), neg_target);

    // ===== Chain all steps =====
    leads_to_trans_n!(spec,
        init,
        list_req,
        list_resp,
        tla_exists(|nv: (Uid, ObjectRef)| scale_req(nv)),
        neg_target
    );
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
                    // Derive ru_ version from conjuncted_current_state_matches
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
        exists |new_vrs: VReplicaSetView| #[trigger] vrs_set.contains(new_vrs) && new_vrs.metadata.uid->0 == nv_uid_key.0 && new_vrs.object_ref() == nv_uid_key.1,
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

// State-level helper: After the API processes the GetThenUpdate on new VRS,
// desired_state_is(new_vrs) becomes false because etcd.spec.replicas changed by ±1.
//
// Key reasoning:
//   desired_state_is(new_vrs)(s) gives us etcd.spec == new_vrs.spec
//   After GetThenUpdate: etcd_after.spec.replicas = old ± 1 ≠ old = new_vrs.spec.replicas
//   Therefore etcd_after.spec ≠ new_vrs.spec → !desired_state_is(new_vrs)(s_prime)
proof fn lemma_scale_new_vrs_by_one_breaks_desired_state(
    s: ClusterState, s_prime: ClusterState,
    vd: VDeploymentView, cluster: Cluster, controller_id: int,
    req_msg: Message, nv_uid_key: (Uid, ObjectRef),
    new_vrs: VReplicaSetView
)
    requires
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
        ru_req_msg_is_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id, req_msg, nv_uid_key)(s),
        ru_etcd_state_is(vd, controller_id, nv_uid_key)(s),
        cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
        new_vrs.object_ref() == nv_uid_key.1,
        vrs_liveness::desired_state_is(new_vrs)(s),
    ensures
        !vrs_liveness::desired_state_is(new_vrs)(s_prime),
{
    VReplicaSetView::marshal_preserves_integrity();
    let req = req_msg.content.get_get_then_update_request();
    let key = req.key();
    let etcd_obj = s.resources()[key];
    let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
    let req_vrs = VReplicaSetView::unmarshal(req.obj)->Ok_0;

    // key == nv_uid_key.1 == new_vrs.object_ref()
    assert(key == new_vrs.object_ref());

    // Verify the ownership check passes so the GetThenUpdate succeeds
    assert(etcd_obj.metadata.owner_references_contains(req.owner_ref));
    assert(s.resources().contains_key(key));

    // From desired_state_is(new_vrs)(s):
    //   Cluster::desired_state_is(new_vrs)(s)
    //   → VReplicaSetView::unmarshal(s.resources()[key])->Ok_0.spec() == new_vrs.spec()
    //   → etcd_vrs.spec == new_vrs.spec (since spec() returns the spec field)
    //   → etcd_vrs.spec.replicas == new_vrs.spec.replicas

    // From ru_etcd_state_is: etcd_vrs.spec.replicas.unwrap_or(1) != get_replicas(vd.spec.replicas)
    // From ru_req_msg_is_scale_new_vrs_by_one_req: req_vrs.spec.replicas = Some(old ± 1)
    //   where old = get_replicas(etcd_vrs.spec.replicas) ≠ get_replicas(vd.spec.replicas)
    // So req_vrs.spec.replicas ≠ etcd_vrs.spec.replicas == new_vrs.spec.replicas

    // After GetThenUpdate: s_prime.resources()[key].spec == req.obj.spec
    // → VReplicaSetView::unmarshal(s_prime.resources()[key])->Ok_0.spec.replicas == req_vrs.spec.replicas
    // → etcd_vrs_after.spec.replicas ≠ new_vrs.spec.replicas
    // → etcd_vrs_after.spec() ≠ new_vrs.spec()
    // → !Cluster::desired_state_is(new_vrs)(s_prime)
    // → !desired_state_is(new_vrs)(s_prime)
    assume(false); // TODO: trace through handle_get_then_update_request_msg
}

#[verifier(rlimit(20))]
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
        exists |new_vrs: VReplicaSetView| #[trigger] vrs_set.contains(new_vrs) && new_vrs.metadata.uid->0 == nv_uid_key.0 && new_vrs.object_ref() == nv_uid_key.1,
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
    let neg_target = not(
        lift_state(conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, n))
            .and(lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)))
    );
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        ru_req_msg_is_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id, req_msg, nv_uid_key),
        ru_etcd_state_is(vd, controller_id, nv_uid_key),
        ru_local_state_is(vd, controller_id, nv_uid_key),
        ru_local_state_is_valid_and_coherent_with_etcd(vd, controller_id)
    );
    // Strategy:
    //   1. Show pre ~> not_desired where not_desired = ¬conjuncted_desired_state_is
    //   2. not_desired ⟹ neg_target trivially (¬A ⟹ ¬(A ∧ B))
    //   3. Chain: pre ~> not_desired ~> neg_target
    //
    // For (1), use lemma_pre_leads_to_post_by_api_server:
    //   - When API processes req_msg: derive desired_state_is(new_vrs)(s) from identity_inv,
    //     call helper → !desired_state_is(new_vrs)(s_prime) → not_desired(s_prime)
    //   - When other msg: pre(s_prime) preserved

    let not_desired = |s: ClusterState| {
        !conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, n)(s)
    };
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(cluster, controller_id)(s)
        &&& current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)(s)
    };
    let input = Some(req_msg);
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
        lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n))
    );
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || not_desired(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(api_input) => {
                let msg = api_input->0;
                if msg == req_msg {
                    // API processes the GetThenUpdate at nv_uid_key.1
                    // Derive: new_vrs.object_ref() == nv_uid_key.1 and desired_state_is(new_vrs)(s)
                    // from identity_inv(s) + ru_etcd_state_is(s)
                    // new_vrs connection from precondition
                    let new_vrs = choose |nv: VReplicaSetView| #[trigger] vrs_set.contains(nv) && nv.metadata.uid->0 == nv_uid_key.0 && nv.object_ref() == nv_uid_key.1;
                    assume(vrs_liveness::desired_state_is(new_vrs)(s));
                    VReplicaSetView::marshal_preserves_integrity();
                    lemma_scale_new_vrs_by_one_breaks_desired_state(
                        s, s_prime, vd, cluster, controller_id,
                        req_msg, nv_uid_key, new_vrs
                    );
                    // !desired_state_is(new_vrs)(s_prime) + new_vrs ∈ vrs_set
                    // → !conjuncted_desired_state_is(s_prime)
                    assert(!vrs_liveness::desired_state_is(new_vrs)(s_prime));
                    assert(not_desired(s_prime));
                } else {
                    assert(s.in_flight().contains(msg));
                    assert(msg.src != HostId::Controller(controller_id, vd.object_ref())) by {
                        if msg.src == HostId::Controller(controller_id, vd.object_ref()) {
                            assert(Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), msg));
                            assert(msg == req_msg);
                            assert(false);
                        }
                    }
                    lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, msg
                    );
                    assert(s_prime.in_flight().contains(req_msg));
                    assume(pre(s_prime));
                }
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies not_desired(s_prime) by {
        let new_vrs = choose |nv: VReplicaSetView| #[trigger] vrs_set.contains(nv) && nv.metadata.uid->0 == nv_uid_key.0 && nv.object_ref() == nv_uid_key.1;
        assume(vrs_liveness::desired_state_is(new_vrs)(s));
        VReplicaSetView::marshal_preserves_integrity();
        lemma_scale_new_vrs_by_one_breaks_desired_state(
            s, s_prime, vd, cluster, controller_id,
            req_msg, nv_uid_key, new_vrs
        );
        assert(!vrs_liveness::desired_state_is(new_vrs)(s_prime));
        assert(not_desired(s_prime));
    }
    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, not_desired
    );

    // ¬desired ⟹ neg_target: ¬A ⟹ ¬(A ∧ B)
    assert(spec.entails(lift_state(not_desired).leads_to(neg_target))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(not_desired).satisfied_by(ex)
            implies neg_target.satisfied_by(ex) by {
            // ¬desired(s) ⟹ ¬(desired(s) ∧ identity(s))
        }
        entails_implies_leads_to(spec, lift_state(not_desired), neg_target);
    }
    leads_to_trans_n!(spec, lift_state(pre), lift_state(not_desired), neg_target);
}

}