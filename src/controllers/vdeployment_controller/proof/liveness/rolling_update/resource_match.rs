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
    trusted::{spec_types::*, step::*, liveness_theorem::*, rely_guarantee::*},
    model::{install::*, reconciler::*},
    proof::{predicate::*, liveness::{api_actions::*, resource_match::*}, helper_lemmas::*, helper_invariants},
    proof::liveness::rolling_update::{predicate::*, composition::*, helper_lemmas::*}
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use crate::reconciler::spec::io::*;
use crate::vstd_ext::{seq_lib::*, set_lib::*};
use vstd::{seq_lib::*, map_lib::*, multiset::*};
use vstd::prelude::*;

verus !{

pub proof fn lemma_from_init_to_not_desired_state_is(vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, new_vrs: VReplicaSetView, diff: nat)
requires
    diff > 0,
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
    spec.entails(tla_forall((|i| cluster.external_next().weak_fairness((controller_id, i))))),
    spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
    spec.entails(always(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)))),
    spec.entails(always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)))),
    spec.entails(always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs.object_ref())))),
ensures
    spec.entails(lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Init]),
        no_pending_req_in_cluster(vd, controller_id)
    )).leads_to(not(
        lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff))
        .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs.object_ref())))
    ))),
{
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
    let list_req_msg = |msg| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        req_msg_is_pending_list_req_in_flight(vd, controller_id, msg)
    ));
    // list_req == \E |msg| list_req_msg(msg)
    assert(list_req == tla_exists(list_req_msg)) by {
        assert forall |ex| #[trigger] list_req.satisfied_by(ex) implies tla_exists(list_req_msg).satisfied_by(ex) by {
            let req_msg = ex.head().ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
            assert((|msg| list_req_msg(msg))(req_msg).satisfied_by(ex));
        }
        temp_pred_equality(list_req, tla_exists(list_req_msg));
    }
    let list_resp = lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        ru_exists_pending_list_resp_in_flight_and_match_req(vd, controller_id, new_vrs.object_ref())
    ));
    // \A |msg| (list_req_msg(msg) ~> list_resp)
    assert forall |req_msg: Message| #[trigger] spec.entails(list_req_msg(req_msg).leads_to(list_resp)) by {
        lemma_from_after_send_list_vrs_req_to_receive_list_vrs_resp_with_nv(vd, spec, cluster, controller_id, req_msg, new_vrs, diff);
    };
    // \A |msg| (list_req_msg(msg) ~> list_resp) |= (\E |msg| list_resp_msg(msg)) ~> list_resp
    leads_to_exists_intro(spec, list_req_msg, list_resp);
    let list_resp_msg = |msg| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        ru_resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, msg, new_vrs.object_ref())
    ));
    // list_resp == \E |msg| list_resp_msg(msg)
    assert(list_resp == tla_exists(list_resp_msg)) by {
        // list_resp |= \E |msg| list_resp_msg(msg)
        assert forall |ex| #[trigger] list_resp.satisfied_by(ex) implies tla_exists(list_resp_msg).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
            let resp_msg = choose |resp_msg| {
                &&& #[trigger] s.in_flight().contains(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& ru_resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s, new_vrs.object_ref())
            };
            assert((list_resp_msg)(resp_msg).satisfied_by(ex));
        }
        temp_pred_equality(list_resp, tla_exists(list_resp_msg));
    };
    // since here, the path diverges from the proof of ESR
    // because we have stronger cluster environment assumption
    leads_to_trans(spec,
        init,
        list_req,
        list_resp
    );
    let scale_nv_req = lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        local_state_at_after_scale_vrs(vd, controller_id, new_vrs.object_ref()),
        ru_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id)
    ));
    assert forall |msg| spec.entails(#[trigger] list_resp_msg(msg).leads_to(scale_nv_req)) by {
        lemma_from_after_receive_list_resp_to_after_scale_new_vrs_with_nv(
            vd, spec, cluster, controller_id, msg, new_vrs, diff
        );
    }
    leads_to_exists_intro(spec, list_resp_msg, scale_nv_req);
    let scale_nv_req_msg = |msg| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        local_state_at_after_scale_vrs(vd, controller_id, new_vrs.object_ref()),
        ru_req_msg_is_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id, msg)
    ));
    assert(scale_nv_req == tla_exists(scale_nv_req_msg)) by {
        assert forall |ex| #[trigger] scale_nv_req.satisfied_by(ex) implies tla_exists(scale_nv_req_msg).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
            assert((scale_nv_req_msg)(req_msg).satisfied_by(ex));
        }
        temp_pred_equality(scale_nv_req, tla_exists(scale_nv_req_msg));
    };
    let neg_post = not(
        lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff))
        .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs.object_ref())))
    );
    assert forall |msg| spec.entails(#[trigger] scale_nv_req_msg(msg).leads_to(neg_post)) by {
        let pre_post = not(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)));
        assert(spec.entails(scale_nv_req_msg(msg).leads_to(pre_post))) by {
            lemma_from_after_scale_new_vrs_to_not_desired_state_with_nv(
                vd, spec, cluster, controller_id, msg, new_vrs, diff
            );
        }
        entails_implies_leads_to(spec, pre_post, neg_post);
        leads_to_trans(spec, scale_nv_req_msg(msg), pre_post, neg_post);
    }
    leads_to_exists_intro(spec, scale_nv_req_msg, neg_post);
    leads_to_trans_n!(spec, init, list_resp, scale_nv_req, neg_post);
}

// same as lemma_from_after_send_list_vrs_req_to_receive_list_vrs_resp with stronger post
pub proof fn lemma_from_after_send_list_vrs_req_to_receive_list_vrs_resp_with_nv(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, req_msg: Message, new_vrs: VReplicaSetView, diff: nat
)
requires
    diff > 0,
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)))),
    spec.entails(always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs.object_ref())))),
ensures
    spec.entails(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]), req_msg_is_pending_list_req_in_flight(vd, controller_id, req_msg)))
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]), ru_exists_pending_list_resp_in_flight_and_match_req(vd, controller_id, new_vrs.object_ref()))))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        req_msg_is_pending_list_req_in_flight(vd, controller_id, req_msg)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        ru_exists_pending_list_resp_in_flight_and_match_req(vd, controller_id, new_vrs.object_ref())
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)(s)
        &&& inductive_current_state_matches(vd, controller_id, new_vrs.object_ref())(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
        lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)),
        lift_state(inductive_current_state_matches(vd, controller_id, new_vrs.object_ref()))
    );
    let input = Some(req_msg);
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                if msg == req_msg {
                    let resp_msg = lemma_list_vrs_request_returns_ok_with_objs_matching_vd_with_nv_status_matching_replicas(
                        s, s_prime, vd, cluster, controller_id, msg, new_vrs, diff
                    );
                    // instantiate existential quantifier.
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& ru_resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s_prime, new_vrs.object_ref())
                    });
                }
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let msg = input->0;
        let resp_msg = lemma_list_vrs_request_returns_ok_with_objs_matching_vd_with_nv_status_matching_replicas(
            s, s_prime, vd, cluster, controller_id, msg, new_vrs, diff
        );
        // instantiate existential quantifier.
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& ru_resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s_prime, new_vrs.object_ref())
        });
    }
    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(50))]
pub proof fn lemma_from_after_receive_list_resp_to_after_scale_new_vrs_with_nv(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message, new_vrs: VReplicaSetView, diff: nat
)
requires
    diff > 0,
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    spec.entails(always(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)))),
    spec.entails(always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)))),
    spec.entails(always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs.object_ref())))),
ensures
    spec.entails(lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        ru_resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg, new_vrs.object_ref())
    )).leads_to(lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        local_state_at_after_scale_vrs(vd, controller_id, new_vrs.object_ref()),
        ru_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id)
    )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        ru_resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg, new_vrs.object_ref())
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        local_state_at_after_scale_vrs(vd, controller_id, new_vrs.object_ref()),
        ru_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(cluster, controller_id)(s)
        &&& desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)(s)
        &&& current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)(s)
        &&& inductive_current_state_matches(vd, controller_id, new_vrs.object_ref())(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself(controller_id),
        lifted_vd_rely_condition(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
        lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)),
        lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)),
        lift_state(inductive_current_state_matches(vd, controller_id, new_vrs.object_ref()))
    );
    let input = (Some(resp_msg), Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                let vrs_list = objects_to_vrs_list(resp_objs)->0;
                let managed_vrs_list = vrs_list.filter(|vrs| valid_owned_vrs(vrs, vd));
                assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies {
                    let key = vrs.object_ref();
                    let etcd_obj = s_prime.resources()[key];
                    let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
                    &&& s_prime.resources().contains_key(key)
                    &&& VReplicaSetView::unmarshal(etcd_obj) is Ok
                    &&& valid_owned_obj_key(vd, s_prime)(key)
                    &&& etcd_vrs.metadata.without_resource_version() == vrs.metadata.without_resource_version()
                    &&& etcd_vrs.spec == vrs.spec
                } by {
                    lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, msg
                    );
                }
                assert(filter_obj_keys_managed_by_vd(vd, s) == filter_obj_keys_managed_by_vd(vd, s_prime)) by {
                    lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, msg, None // just need the first post condition
                    );
                }
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == Some(resp_msg) && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    VReplicaSetView::marshal_preserves_integrity();
                    let etcd_vrs = VReplicaSetView::unmarshal(s.resources()[new_vrs.object_ref()])->Ok_0;
                    if get_replicas(etcd_vrs.spec.replicas) == get_replicas(vd.spec.replicas) {
                        assert(false); // diff > 0
                    }
                    if get_replicas(etcd_vrs.spec.replicas) == 0 {
                        assert(get_replicas(vd.spec.replicas) >= 0);
                        if get_replicas(vd.spec.replicas) != 0 {
                            assert(false); // diff > 0
                        } else {
                            assert(false); // vd > 0 ==> vrs > 0
                        }
                    }
                    lemma_from_list_resp_with_nv_status_matching_spec_to_next_state(
                        s, s_prime, vd, cluster, controller_id, resp_msg, new_vrs.object_ref()
                    );
                }
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        VDeploymentReconcileState::marshal_preserves_integrity();
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

#[verifier(rlimit(100))]
#[verifier(spinoff_prover)]
pub proof fn lemma_from_after_scale_new_vrs_to_not_desired_state_with_nv(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, req_msg: Message, new_vrs: VReplicaSetView, diff: nat
)
requires
    diff > 0,
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
    spec.entails(always(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)))),
    spec.entails(always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)))),
    spec.entails(always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs.object_ref())))),
ensures
    spec.entails(lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        local_state_at_after_scale_vrs(vd, controller_id, new_vrs.object_ref()),
        ru_req_msg_is_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id, req_msg)
    )).leads_to(not(
        lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff))
    ))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        local_state_at_after_scale_vrs(vd, controller_id, new_vrs.object_ref()),
        ru_req_msg_is_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id, req_msg)
    );
    let post = |s: ClusterState| {
        !desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)(s)
    };
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& vd_rely_condition(cluster, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)(s)
        &&& current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)(s)
        &&& inductive_current_state_matches(vd, controller_id, new_vrs.object_ref())(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_rely_condition(cluster, controller_id),
        lifted_vd_reconcile_request_only_interferes_with_itself(controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
        lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)),
        lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)),
        lift_state(inductive_current_state_matches(vd, controller_id, new_vrs.object_ref()))
    );
    let input = Some(req_msg);
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                if msg != req_msg {
                    assert(s.resources().contains_key(new_vrs.object_ref())); // trigger
                    lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, msg
                    ); // new_vrs in etcd is not updated
                }
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.2 == Some(vd.object_ref()) {}
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
    }
    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
    temp_pred_equality(
        lift_state(post),
        not(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)))
    );
}


pub proof fn lemma_from_list_resp_with_nv_status_matching_spec_to_next_state(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, resp_msg: Message, new_vrs_key: ObjectRef
)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp_msg), Some(vd.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s),
    ru_resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg, new_vrs_key)(s),
    inductive_current_state_matches(vd, controller_id, new_vrs_key)(s),
    // from diff != 0
    get_replicas(VReplicaSetView::unmarshal(s.resources()[new_vrs_key])->Ok_0.spec.replicas) > 0,
    get_replicas(VReplicaSetView::unmarshal(s.resources()[new_vrs_key])->Ok_0.spec.replicas) != get_replicas(vd.spec.replicas)
ensures
    at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS])(s_prime),
    local_state_at_after_scale_vrs(vd, controller_id, new_vrs_key)(s_prime),
    ru_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id)(s_prime),
{
    lemma_esr_equiv_to_instantiated_etcd_state_is_with_nv_key(
        vd, cluster, controller_id, new_vrs_key, s
    );
    VDeploymentReconcileState::marshal_preserves_integrity();
    VReplicaSetView::marshal_preserves_integrity();
    broadcast use group_seq_properties;
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    let etcd_obj = s.resources()[new_vrs_key];
    let etcd_new_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
    assert(objects_to_vrs_list(resp_objs) is Some);
    let key_map = |vrs: VReplicaSetView| vrs.object_ref();
    let vrs_list = objects_to_vrs_list(resp_objs)->0;
    let managed_vrs_list = objects_to_vrs_list(resp_objs)->0.filter(|vrs| valid_owned_vrs(vrs, vd));
    let (new_vrs_or_none, old_vrs_list) = filter_old_and_new_vrs(vd, managed_vrs_list);
    let new_vrs_uid = Some(etcd_new_vrs.metadata.uid->0);
    let valid_owned_vrs_filter = |vrs: VReplicaSetView| valid_owned_vrs(vrs, vd);
    let managed_vrs_list = vrs_list.filter(valid_owned_vrs_filter);
    let nonempty_vrs_filter = |vrs: VReplicaSetView| vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0;
    let old_vrs_filter = |vrs: VReplicaSetView| {
        &&& new_vrs_uid is None || vrs.metadata.uid->0 != new_vrs_uid->0
        &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
    };
    assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies {
        &&& vrs.metadata.name is Some
        &&& vrs.metadata.uid is Some
        &&& vrs.metadata.namespace is Some
        &&& exists |i: int| #![trigger resp_objs[i]] 0 <= i < resp_objs.len() && VReplicaSetView::unmarshal(resp_objs[i])->Ok_0 == vrs
    } by {
        seq_filter_is_a_subset_of_original_seq(vrs_list, |vrs| valid_owned_vrs(vrs, vd));
        assert(exists |i| 0 <= i < vrs_list.len() && #[trigger] vrs_list[i] == vrs);
        let i = choose |i| 0 <= i < vrs_list.len() && #[trigger] vrs_list[i] == vrs;
        assert(resp_objs.contains(resp_objs[i])); // trigger
        assert(vrs_list == resp_objs.map_values(|o| VReplicaSetView::unmarshal(o)->Ok_0));
        assert(vrs_list[i] == VReplicaSetView::unmarshal(resp_objs[i])->Ok_0);
        VReplicaSetView::marshal_preserves_metadata();
    }
    if new_vrs_or_none is None { // prove contradiction
        assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).len() == 0);
        seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(managed_vrs_list, match_template_without_hash(vd.spec.template));
        if exists |k: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(k)
            &&& valid_owned_obj_key(vd, s)(k)
            &&& filter_new_vrs_keys(vd.spec.template, s)(k)
        }{
            let k = choose |k: ObjectRef| {
                &&& #[trigger] s.resources().contains_key(k)
                &&& valid_owned_obj_key(vd, s)(k)
                &&& filter_new_vrs_keys(vd.spec.template, s)(k)
            };
            assert(filter_obj_keys_managed_by_vd(vd, s).contains(k));
            assert(managed_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref()).contains(k));
            let i = choose |i: int| 0 <= i < managed_vrs_list.len() && #[trigger] managed_vrs_list.map_values(key_map)[i] == k;
            let vrs = managed_vrs_list[i];
            assert(vrs.object_ref() == k);
            assert(managed_vrs_list.contains(vrs)); // trigger
            assert(false) by {
                assert(!match_template_without_hash(vd.spec.template)(vrs));
                assert(match_template_without_hash(vd.spec.template)(vrs)) by {
                    let etcd_obj = s.resources()[k];
                    let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
                    assert(match_template_without_hash(vd.spec.template)(etcd_vrs));
                    assert(etcd_vrs.spec == vrs.spec);
                }
            }
        }
    }
    assert(new_vrs_or_none is Some);
    let new_vrs = new_vrs_or_none->0;
    assert(managed_vrs_list.contains(new_vrs)) by { // trigger
        seq_filter_is_a_subset_of_original_seq(managed_vrs_list, match_template_without_hash(vd.spec.template));
        if managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(nonempty_vrs_filter).len() > 0 {
            seq_filter_is_a_subset_of_original_seq(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)), nonempty_vrs_filter); 
        }
    }
    if new_vrs.object_ref() != new_vrs_key {
        assert(get_replicas(etcd_new_vrs.spec.replicas) > 0);
        // vrs with nv_uid_key can pass the nonempty_vrs_filter, it's impossible for new_vrs to be selected here
        assert(new_vrs.metadata.uid->0 != etcd_new_vrs.metadata.uid->0);
        assert(valid_owned_obj_key(vd, s)(new_vrs.object_ref()));
        assert(filter_obj_keys_managed_by_vd(vd, s).contains(new_vrs_key));
        assert(managed_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref()).contains(new_vrs_key));
        let i = choose |i: int| 0 <= i < managed_vrs_list.len() && #[trigger] managed_vrs_list.map_values(key_map)[i] == new_vrs_key;
        let vrs = managed_vrs_list[i];
        assert(vrs.object_ref() == new_vrs_key);
        assert(managed_vrs_list.contains(vrs)); // trigger
        assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(nonempty_vrs_filter).contains(vrs)) by {
            assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).contains(vrs)); // trigger
        }
        assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(nonempty_vrs_filter).len() > 0);
        assert(!managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(nonempty_vrs_filter).contains(new_vrs));
        assert(false);
    }
    assert(new_vrs.status is Some && new_vrs.status->0.replicas == get_replicas(new_vrs.spec.replicas)) by {
        assert(exists |vrs| {
            &&& #[trigger] managed_vrs_list.contains(vrs)
            &&& vrs.object_ref() == new_vrs_key
            &&& vrs.status is Some
            &&& vrs.status->0.replicas == get_replicas(vrs.spec.replicas)
        });
        let pretend_to_be_non_new_vrs = choose |vrs| {
            &&& #[trigger] managed_vrs_list.contains(vrs)
            &&& vrs.object_ref() == new_vrs_key
            &&& vrs.status is Some
            &&& vrs.status->0.replicas == get_replicas(vrs.spec.replicas)
        };
        if pretend_to_be_non_new_vrs != new_vrs {
            VReplicaSetView::marshal_preserves_integrity();
            let i = choose |i: int| #![trigger resp_objs[i]] 0 <= i < resp_objs.len() && #[trigger] VReplicaSetView::unmarshal(resp_objs[i])->Ok_0 == pretend_to_be_non_new_vrs;
            let j = choose |j: int| #![trigger resp_objs[j]] 0 <= j < resp_objs.len() && #[trigger] VReplicaSetView::unmarshal(resp_objs[j])->Ok_0 == new_vrs;
            assert(resp_objs.contains(resp_objs[i]));
            assert(resp_objs.contains(resp_objs[j])); // trigger
            assert(resp_objs[i].object_ref() == new_vrs_key);
            assert(resp_objs[j].object_ref() == new_vrs_key);
            if i == j {
                assert(pretend_to_be_non_new_vrs == new_vrs);
                assert(false);
            }
            assert(resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref()).no_duplicates());
            assert(resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref())[i] == resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref())[j]);
            assert(false);
        }
    }
}

// this is dedicated for inductivity proof, for rank decrease proof, use the stronger version above
// TODO: merge with lemma_from_list_resp_to_next_state?
pub proof fn lemma_from_list_resp_with_nv_to_next_state(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, resp_msg: Message, nv_uid_key_replicas_status: (Uid, ObjectRef, int, Option<int>), new_vrs_key: ObjectRef
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp_msg), Some(vd.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s),
    resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg)(s),
    ru_new_vrs_and_no_old_vrs_from_resp_objs(vd, controller_id, resp_msg, nv_uid_key_replicas_status, new_vrs_key)(s),
ensures
    if (nv_uid_key_replicas_status.2 == 0 || (nv_uid_key_replicas_status.3 is Some && nv_uid_key_replicas_status.3->0 == nv_uid_key_replicas_status.2)) && nv_uid_key_replicas_status.2 != get_replicas(vd.spec.replicas) { // mismatch_replicas
        &&& at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS])(s_prime)
        &&& local_state_at_after_scale_vrs(vd, controller_id, new_vrs_key)(s_prime)
        &&& ru_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id)(s_prime)
        &&& nv_uid_key_replicas_status.1 == new_vrs_key
    } else {
        &&& at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS])(s_prime)
        &&& local_state_is(vd, controller_id, Some((nv_uid_key_replicas_status.0, nv_uid_key_replicas_status.1, nv_uid_key_replicas_status.2)), 0)(s_prime)
        &&& no_pending_req_in_cluster(vd, controller_id)(s_prime)
    },
    ({ // for additional requirements in inductive csm
        let local_state_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        let etcd_vrs = VReplicaSetView::unmarshal(s.resources()[new_vrs_key])->Ok_0;
        &&& local_state_prime.new_vrs is Some
        &&& get_replicas(etcd_vrs.spec.replicas) > 0 ==> {
            &&& local_state_prime.new_vrs->0.object_ref() == new_vrs_key
            &&& local_state_prime.new_vrs->0.metadata.uid->0 == etcd_vrs.metadata.uid->0
        }
        &&& local_state_prime.new_vrs->0.object_ref() != new_vrs_key ==> {
            &&& get_replicas(local_state_prime.new_vrs->0.spec.replicas) == 0
        }
    }),
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    VReplicaSetView::marshal_preserves_integrity();
    broadcast use group_seq_properties;
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    assert(objects_to_vrs_list(resp_objs) is Some);
    let vrs_list = objects_to_vrs_list(resp_objs)->0;
    let managed_vrs_list = objects_to_vrs_list(resp_objs)->0.filter(|vrs| valid_owned_vrs(vrs, vd));
    let (new_vrs_or_none, old_vrs_list) = filter_old_and_new_vrs(vd, managed_vrs_list);
    let new_vrs_uid = Some(nv_uid_key_replicas_status.0);
    let valid_owned_vrs_filter = |vrs: VReplicaSetView| valid_owned_vrs(vrs, vd);
    let managed_vrs_list = vrs_list.filter(valid_owned_vrs_filter);
    assert(new_vrs_or_none is Some);
    let new_vrs = new_vrs_or_none->0;
    assert forall |vrs| #[trigger] vrs_list.contains(vrs) implies vrs.metadata.uid is Some by {
        let i = choose |i: int| 0 <= i < vrs_list.len() && vrs_list[i] == vrs;
        VReplicaSetView::marshal_preserves_metadata();
        assert(resp_objs.contains(resp_objs[i])); // trigger
        assert(VReplicaSetView::unmarshal(resp_objs[i]) is Ok);
        assert(vrs_list[i] == VReplicaSetView::unmarshal(resp_objs[i])->Ok_0);
    }
    assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies vrs.metadata.uid is Some by {
        seq_filter_is_a_subset_of_original_seq(vrs_list, valid_owned_vrs_filter);
    }
    let old_vrs_list_filter_with_new_vrs = |vrs: VReplicaSetView| {
        &&& new_vrs_or_none is None || vrs.metadata.uid != new_vrs.metadata.uid
        &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
    };
    let another_filter_used_in_esr = |vrs: VReplicaSetView| {
        &&& new_vrs_uid is None || vrs.metadata.uid->0 != new_vrs_uid->0
        &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
    };
    assert(old_vrs_list == managed_vrs_list.filter(old_vrs_list_filter_with_new_vrs));
    // because in reconciler we don't know all objects has uid, which is guaranteed by cluster env predicates
    // so the filter in reconciler didn't use uid->0
    assert(managed_vrs_list.filter(old_vrs_list_filter_with_new_vrs) == managed_vrs_list.filter(another_filter_used_in_esr)) by {
        assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies
            (old_vrs_list_filter_with_new_vrs(vrs) == another_filter_used_in_esr(vrs)) by {
            assert(vrs.metadata.uid is Some);
            assert(new_vrs_uid is Some);
            assert(new_vrs.metadata.uid == new_vrs_uid);
        }
        same_filter_implies_same_result(managed_vrs_list, old_vrs_list_filter_with_new_vrs, another_filter_used_in_esr);
    }
    assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies vrs_list.contains(vrs) && valid_owned_vrs(vrs, vd) by {
        seq_filter_is_a_subset_of_original_seq(vrs_list, valid_owned_vrs_filter);
    }
    assert forall |vrs: VReplicaSetView| #[trigger] old_vrs_list.contains(vrs) implies
        vrs_list.contains(vrs) && valid_owned_vrs(vrs, vd) && s.resources().contains_key(vrs.object_ref()) by {
        seq_filter_is_a_subset_of_original_seq(managed_vrs_list, old_vrs_list_filter_with_new_vrs);
    }
    assert(managed_vrs_list.contains(new_vrs) && vrs_list.contains(new_vrs) && valid_owned_vrs(new_vrs, vd) && match_template_without_hash(vd.spec.template)(new_vrs)) by {
        assert(managed_vrs_list.contains(new_vrs) && match_template_without_hash(vd.spec.template)(new_vrs)) by { // trigger
            // unwrap filter_old_and_new_vrs
            let non_zero_replicas_filter = |vrs: VReplicaSetView| vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0;
            if managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).len() > 0 {
                seq_filter_is_a_subset_of_original_seq(managed_vrs_list, match_template_without_hash(vd.spec.template));
                if managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(non_zero_replicas_filter).len() > 0 {
                    assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(non_zero_replicas_filter).contains(new_vrs));
                    seq_filter_is_a_subset_of_original_seq(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)), non_zero_replicas_filter);
                }
                assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).contains(new_vrs));
            } else {
                assert(new_vrs_or_none is None);
                assert(false);
            }
        }
    };
    let map_key = |vrs: VReplicaSetView| vrs.object_ref();
    assert(old_vrs_list.map_values(map_key).no_duplicates()) by { // triggering_cr.well_formed()
        let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
        lemma_no_duplication_in_resp_objs_implies_no_duplication_in_down_stream(triggering_cr, resp_objs);
    }
    assert(old_vrs_list.map_values(map_key).to_set()
        == filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(new_vrs_uid, s))) by {
        lemma_old_vrs_filter_on_objs_eq_filter_on_keys(vd, managed_vrs_list, new_vrs_uid, s);
    }
    assert(old_vrs_list.len() == 0) by {
        old_vrs_list.map_values(map_key).unique_seq_to_set();
        assert(old_vrs_list.map_values(map_key).len() == old_vrs_list.len());
        assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(new_vrs_uid, s)).len() == 0);
    }

    let vds = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    let vds_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    assert(vds_prime.old_vrs_list == old_vrs_list);
    assert(vds_prime.old_vrs_index == old_vrs_list.len());

    // prove local_state_is_coherent_with_etcd_valid_and_coherent(s_prime)
    assert forall |i| #![trigger vds_prime.old_vrs_list[i]] 0 <= i < vds_prime.old_vrs_index
        implies managed_vrs_list.contains(vds_prime.old_vrs_list[i]) by {
        assert(old_vrs_list.contains(vds_prime.old_vrs_list[i])); // trigger
    }
}

}