use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    api_server::types::*,
    cluster::*, 
    message::*
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::{
    trusted::{spec_types::*, step::*, util::*, liveness_theorem::*},
    model::{install::*, reconciler::*},
    proof::{predicate::*, liveness::api_actions::*},
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use crate::reconciler::spec::io::*;
use vstd::prelude::*;

verus !{

pub proof fn lemma_from_init_to_current_state_matches(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
ensures
    spec.entails(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(Init)), no_pending_req_in_cluster(vd, controller_id)))
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(Done)), current_state_matches(vd))))),
{
    let inv = {
        &&& spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))))
        &&& spec.entails(always(lift_action(cluster.next())))
        &&& spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i)))
        &&& spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1))))
    };
    // init ~> send list req
    let init = lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(Init)), no_pending_req_in_cluster(vd, controller_id)));
    lemma_from_init_step_to_send_list_vrs_req(vd, spec, cluster, controller_id);
    // send list req ~> exists |msg| msg_is_list_req(msg)
    // just to make verus happy with trigger on macro
    let list_req = lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)), pending_list_req_in_flight(vd, controller_id)));
    let msg_is_list_req = |msg| lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)), req_msg_is_the_pending_list_req_in_flight(vd, controller_id, msg)));
    assert(spec.entails(list_req.leads_to(tla_exists(|msg| msg_is_list_req(msg))))) by {
        assert forall |ex| #[trigger] list_req.satisfied_by(ex) implies
            tla_exists(|msg| msg_is_list_req(msg)).satisfied_by(ex) by {
            let req_msg = ex.head().ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0();
            tla_exists_proved_by_witness(ex, |msg| msg_is_list_req(msg), req_msg);
        }
        entails_implies_leads_to(spec, list_req, tla_exists(|msg| msg_is_list_req(msg)));
    }
    // forall |msg| msg_is_list_req(msg) ~> exists_pending_list_resp_in_flight_and_match_req
    let exists_list_resp = lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
            exists_pending_list_resp_in_flight_and_match_req(vd, controller_id)
    ));
    assert forall |req_msg: Message| inv implies #[trigger] spec.entails(msg_is_list_req(req_msg).leads_to(exists_list_resp)) by {
        lemma_from_after_send_list_vrs_req_to_receive_list_vrs_resp(vd, spec, cluster, controller_id, req_msg);
    };
    let msg_is_list_resp = |msg| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, msg)
    ));
    leads_to_exists_intro(spec, |req_msg| msg_is_list_req(req_msg), exists_list_resp);
    assert(spec.entails(exists_list_resp.leads_to(tla_exists(|msg| msg_is_list_resp(msg))))) by {
        assert forall |ex| #[trigger] exists_list_resp.satisfied_by(ex) implies
            tla_exists(|msg| msg_is_list_resp(msg)).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0();
            let resp_msg = choose |resp_msg| {
                &&& #[trigger] s.in_flight().contains(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& resp_msg_is_ok_list_resp_containing_matched_vrs(s, vd, resp_msg)
            };
            tla_exists_proved_by_witness(ex, |msg| msg_is_list_resp(msg), resp_msg);
        }
        entails_implies_leads_to(spec, exists_list_resp, tla_exists(|msg| msg_is_list_resp(msg)));
    };
    leads_to_trans_n!(
        spec,
        init,
        list_req,
        tla_exists(|msg| msg_is_list_req(msg)),
        exists_list_resp,
        tla_exists(|msg| msg_is_list_resp(msg))
    );
    // path diverges
    assert(forall |resp_msg: Message| #![trigger msg_is_list_resp(resp_msg)] 
        inv ==> spec.entails(msg_is_list_resp(resp_msg).implies(
        lift_state(and!(
            // controller local state machine need to use non-Init step with resp message to transit
            at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
            resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
            should_create_new_vrs(vd)))
        .or(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
            resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
            should_scale_new_vrs(vd))))
        .or(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
            resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
            should_scale_down_old_vrs(vd))))
        .or(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
            resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
            should_scale_down_old_vrs_with_diff(vd, nat0!())))
        ))
    ));
    // TODO: prove as long as the current state is not init (and we have message to push controller transition)
    // nothing_to_do ~> Done
    // should_scale_down_old_vrs ~> at_step!(AfterScaleDownOldVRS) ~> (need ranking function) Done
    // should_scale_new_vrs ~> at_step!(AfterScaleNewVRS) ~> at_step!(AfterScaleDownOldVRS) | Done
    // should_create_new_vrs ~> at_step!(AfterCreateNewVRS) ~> at_step!(AfterScaleNewVRS) | at_step!(AfterScaleDownOldVRS) | Done
    assume(false);
}

pub proof fn lemma_from_should_scale_down_old_vrs_with_diff_to_current_state_matches(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message, diff: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    diff > 0,
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterScaleDownOldVRS)),
            resp_msg_is_scale_down_old_vrs_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
            should_scale_down_old_vrs_with_diff(vd, diff)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterScaleDownOldVRS)),
            resp_msg_is_scale_down_old_vrs_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
            should_scale_down_old_vrs_with_diff(vd, diff - nat1!())
        )))),
decreases
    diff,
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterScaleDownOldVRS)),
        resp_msg_is_scale_down_old_vrs_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
        should_scale_down_old_vrs_with_diff(vd, diff)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterScaleDownOldVRS)),
        resp_msg_is_scale_down_old_vrs_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
        should_scale_down_old_vrs_with_diff(vd, diff)
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
    let input = (Some(resp_msg), Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(input) => {
                VDeploymentReconcileState::marshal_preserves_integrity();
            }
            _ => {}
        }
    }
}

pub proof fn lemma_from_old_vrs_len_zero_current_state_matches(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
            resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
            should_scale_down_old_vrs_with_diff(vd, nat0!())
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step!(Done)),
            current_state_matches(vd)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
        should_scale_down_old_vrs_with_diff(vd, nat0!())
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step!(Done)),
        current_state_matches(vd)
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
    let input = (Some(resp_msg), Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                lemma_api_request_other_than_pending_req_msg_maintains_filter_old_and_new_vrs_on_etcd(
                    s, s_prime, vd, cluster, controller_id, input.get_Some_0()
                );
            }
            Step::ControllerStep(..) => {
                VDeploymentReconcileState::marshal_preserves_integrity();
                // TODO: fix this
                // it's possible to transit into Error for other states
                assume(at_vd_step_with_vd(vd, controller_id, at_step!(Done))(s_prime));
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime)
        && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        VDeploymentReconcileState::marshal_preserves_integrity();
    }
    assert forall |s| #[trigger] pre(s) implies cluster.controller_action_pre(ControllerStep::ContinueReconcile, (controller_id, input.0, input.1))(s) by {
        use crate::kubernetes_cluster::spec::network::state_machine::network;
        let host_result = cluster.controller(controller_id).next_action_result(
            (cluster.controller(controller_id).step_to_action)(ControllerStep::ContinueReconcile),
            ControllerActionInput{recv: input.0, scheduled_cr_key: input.1, rpc_id_allocator: s.rpc_id_allocator},
            s.controller_and_externals[controller_id].controller
        );
        let msg_ops = MessageOps {
            recv: input.0,
            send: host_result.get_Enabled_1().send,
        };
        let network_result = network().next_result(msg_ops, s.network);
        assert(cluster.controller_models.contains_key(controller_id));
        assert(input.1.is_Some());
        assert(received_msg_destined_for(input.0, HostId::Controller(controller_id, input.1.get_Some_0())));
        //TODO: fix
        assume(host_result.is_Enabled());
        assert(network_result.is_Enabled());
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
    
}

pub proof fn lemma_from_after_send_list_vrs_req_to_receive_list_vrs_resp(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, req_msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
ensures
    spec.entails(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)), req_msg_is_the_pending_list_req_in_flight(vd, controller_id, req_msg)))
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)), exists_pending_list_resp_in_flight_and_match_req(vd, controller_id))))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
        req_msg_is_the_pending_list_req_in_flight(vd, controller_id, req_msg)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
        exists_pending_list_resp_in_flight_and_match_req(vd, controller_id)
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
    let input = Some(req_msg);
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input.get_Some_0();

                if msg == req_msg {
                    let resp_msg = lemma_list_vrs_request_returns_ok_with_objs_matching_vd(
                        s, s_prime, vd, cluster, controller_id, msg
                    );
                    // instantiate existential quantifier.
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg_is_ok_list_resp_containing_matched_vrs(s_prime, vd, resp_msg)
                    });
                }
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let msg = input.get_Some_0();
        let resp_msg = lemma_list_vrs_request_returns_ok_with_objs_matching_vd(
            s, s_prime, vd, cluster, controller_id, msg,
        );
        // instantiate existential quantifier.
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg_is_ok_list_resp_containing_matched_vrs(s_prime, vd, resp_msg)
        });
    }
    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

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
    spec.entails(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(Init)), no_pending_req_in_cluster(vd, controller_id)))
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)), pending_list_req_in_flight(vd, controller_id))))),
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(Init)),
        no_pending_req_in_cluster(vd, controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
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
    // this assertion makes proof 86% faster
    assert(forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) ==> pre(s_prime) || post(s_prime));
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}
}