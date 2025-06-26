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
    proof::{predicate::*, helper_lemmas::*, liveness::api_actions::*},
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
    let exists_list_resp = lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)), exists_pending_list_resp_in_flight_and_match_req(vd, controller_id)));
    assert forall |req_msg: Message| inv implies #[trigger] spec.entails(msg_is_list_req(req_msg).leads_to(exists_list_resp)) by {
        lemma_from_after_send_list_vrs_req_to_receive_list_vrs_resp(vd, spec, cluster, controller_id, req_msg);
    };
    leads_to_exists_intro(spec, |req_msg| msg_is_list_req(req_msg), exists_list_resp);
    leads_to_trans_n!(
        spec,
        init,
        list_req,
        tla_exists(|msg| msg_is_list_req(msg)),
        exists_list_resp
    );
    // path diverges
    assert(spec.entails(exists_list_resp.implies(
        lift_state(and!(
            // controller local state machine need to use non-Init step with resp message to transit
            at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
            exists_pending_list_resp_in_flight_and_match_req(vd, controller_id),
            should_create_new_vrs(vd)))
        .or(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
            exists_pending_list_resp_in_flight_and_match_req(vd, controller_id),
            should_scale_new_vrs(vd))))
        .or(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
            exists_pending_list_resp_in_flight_and_match_req(vd, controller_id),
            should_scale_down_old_vrs(vd))))
        .or(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
            exists_pending_list_resp_in_flight_and_match_req(vd, controller_id),
            nothing_to_do(vd)))
        ))));
    assume(false);
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
    assert(spec.entails(lift_state(pre).leads_to(lift_state(post)))) by {
        let input = (None::<Message>, Some(vd.object_ref()));
        let stronger_next = |s, s_prime: ClusterState| {
            &&& cluster.next()(s, s_prime)
            &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        };
        combine_spec_entails_always_n!(spec,
            lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
        );
        // this assertion makes proof 86% faster
        assert(forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) ==> pre(s_prime) || post(s_prime));
        cluster.lemma_pre_leads_to_post_by_controller(
            spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
        );
    }
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
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
    );
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

pub proof fn lemma_from_nothing_todo_to_current_state_matches(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
ensures
    spec.entails(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS, AfterCreateNewVRS, AfterScaleNewVRS, AfterScaleDownOldVRS, Done)), nothing_to_do(vd)))
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step!(Done)), current_state_matches(vd))))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS, AfterCreateNewVRS, AfterScaleNewVRS, AfterScaleDownOldVRS, Done)),
        nothing_to_do(vd)
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
    let input = (Some())
    assert(forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) ==> pre(s_prime) || post(s_prime));
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, None, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}
}