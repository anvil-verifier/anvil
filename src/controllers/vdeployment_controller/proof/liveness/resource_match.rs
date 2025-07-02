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
    trusted::{spec_types::*, step::*, util::*, liveness_theorem::*},
    model::{install::*, reconciler::*},
    proof::{predicate::*, liveness::api_actions::*},
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use crate::reconciler::spec::io::*;
use crate::vstd_ext::seq_lib::*;
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
    spec.entails(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or![Init]), no_pending_req_in_cluster(vd, controller_id)))
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or![Done]), current_state_matches(vd))))),
{
    let inv = {
        &&& spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))))
        &&& spec.entails(always(lift_action(cluster.next())))
        &&& spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i)))
        &&& spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1))))
    };
    // init ~> send list req
    let init = lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or![Init]), no_pending_req_in_cluster(vd, controller_id)));
    lemma_from_init_step_to_send_list_vrs_req(vd, spec, cluster, controller_id);
    // send list req ~> exists |msg| msg_is_list_req(msg)
    // just to make verus happy with trigger on macro
    let list_req = lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or![AfterListVRS]), pending_list_req_in_flight(vd, controller_id)));
    let msg_is_list_req = |msg| lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or![AfterListVRS]), req_msg_is_the_pending_list_req_in_flight(vd, controller_id, msg)));
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
        at_vd_step_with_vd(vd, controller_id, at_step_or![AfterListVRS]),
        exists_pending_list_resp_in_flight_and_match_req(vd, controller_id)
    ));
    assert forall |req_msg: Message| inv implies #[trigger] spec.entails(msg_is_list_req(req_msg).leads_to(exists_list_resp)) by {
        lemma_from_after_send_list_vrs_req_to_receive_list_vrs_resp(vd, spec, cluster, controller_id, req_msg);
    };
    let msg_is_list_resp = |msg| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or![AfterListVRS]),
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
    // assert(forall |resp_msg: Message| #![trigger msg_is_list_resp(resp_msg)] 
    //     inv ==> spec.entails(msg_is_list_resp(resp_msg).implies(
    //     lift_state(and!(
    //         // controller local state machine need to use non-Init step with resp message to transit
    //         at_vd_step_with_vd(vd, controller_id, at_step_or![AfterListVRS]),
    //         resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
    //         should_create_new_vrs(vd)))
    //     .or(lift_state(and!(
    //         at_vd_step_with_vd(vd, controller_id, at_step_or![AfterListVRS]),
    //         resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
    //         should_scale_new_vrs(vd))))
    //     .or(lift_state(and!(
    //         at_vd_step_with_vd(vd, controller_id, at_step_or![AfterListVRS]),
    //         resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
    //         should_scale_down_old_vrs(vd))))
    //     .or(lift_state(and!(
    //         at_vd_step_with_vd(vd, controller_id, at_step_or![AfterListVRS]),
    //         resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
    //         should_scale_down_old_vrs_of_n(vd, nat0!())))
    //     ))
    // ));
    // TODO: prove as long as the current state is not init (and we have message to push controller transition)
    // nothing_to_do ~> Done
    // should_scale_down_old_vrs ~> at_step!(AfterScaleDownOldVRS) ~> (need ranking function) Done
    // should_scale_new_vrs ~> at_step!(AfterScaleNewVRS) ~> at_step!(AfterScaleDownOldVRS) | Done
    // should_create_new_vrs ~> at_step!(AfterCreateNewVRS) ~> at_step!(AfterScaleNewVRS) | at_step!(AfterScaleDownOldVRS) | Done
    assume(false);
}

pub proof fn lemma_from_after_send_get_then_update_req_to_receive_get_then_update_resp_on_old_vrs_of_n(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, req_msg: Message, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    n > 0,
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(n - nat1!()))]),
            req_msg_is_pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, req_msg, int0!()),
            with_n_old_vrs_in_etcd(controller_id, vd, n),
            local_state_match_etcd_on_old_vrs_list(vd, controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(n - nat1!()))]),
            exists_resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, int0!()),
            with_n_old_vrs_in_etcd(controller_id, vd, n - nat1!()),
            local_state_match_etcd_on_old_vrs_list(vd, controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(n - nat1!()))]),
        req_msg_is_pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, req_msg, int0!()),
        with_n_old_vrs_in_etcd(controller_id, vd, n),
        local_state_match_etcd_on_old_vrs_list(vd, controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(n - nat1!()))]),
        exists_resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, int0!()),
        with_n_old_vrs_in_etcd(controller_id, vd, n - nat1!()),
        local_state_match_etcd_on_old_vrs_list(vd, controller_id)
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
    // this proof is cursed
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input.get_Some_0();
                if msg == req_msg {
                    let resp_msg = lemma_get_then_update_request_returns_ok_at_after_scale_down_old_vrs(s, s_prime, vd, cluster, controller_id, msg, n);
                    // assert(Cluster::pending_req_msg_is(controller_id, s_prime, vd.object_ref(), req_msg));
                    // assert(req_msg.src == HostId::Controller(controller_id, vd.object_ref()));
                    VReplicaSetView::marshal_preserves_integrity();
                    // let request = req_msg.content.get_APIRequest_0().get_GetThenUpdateRequest_0();
                    // let key = request.key();
                    // let etcd_obj = s_prime.resources()[key];
                    // let req_vrs = VReplicaSetView::unmarshal(request.obj).unwrap();
                    // assert(req_msg.src == HostId::Controller(controller_id, vd.object_ref()));
                    // assert(req_msg.dst == HostId::APIServer);
                    // assert(req_msg.content.is_APIRequest());
                    // assert(req_msg.content.get_APIRequest_0().is_GetThenUpdateRequest());
                    // assert(request.namespace == vd.metadata.namespace.unwrap());
                    // assert(request.owner_ref == vd.controller_owner_ref());
                    // assert(s_prime.resources().contains_key(key));
                    // assert(etcd_obj.kind == VReplicaSetView::kind());
                    // assert(etcd_obj.metadata.namespace == vd.metadata.namespace);
                    // assert(etcd_obj.metadata.owner_references_contains(vd.controller_owner_ref()));
                    // assert(req_vrs.metadata.owner_references_contains(vd.controller_owner_ref()));
                    // assert(req_vrs.spec.replicas.unwrap_or(1) == int0!());
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                    });
                    // assert(exists_resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, int0!())(s_prime));
                    // assert(at_vd_step_with_vd(vd, controller_id, at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(n - nat1!()))])(s_prime));
                    // assert(with_n_old_vrs_in_etcd(controller_id, vd, (n - nat1!()) as nat)(s_prime));
                    // assert(local_state_match_etcd_on_old_vrs_list(vd, controller_id)(s_prime));
                    assert(post(s_prime));
                }
            },
            _ => {
                assert(pre(s_prime));
            }
        }
    }
    assume(false);
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let msg = input.get_Some_0();
        let resp_msg = lemma_get_then_update_request_returns_ok_at_after_scale_down_old_vrs(s, s_prime, vd, cluster, controller_id, msg, n);
        // instantiate existential quantifier.
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        });
    }
    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

pub proof fn lemma_from_at_after_ensure_new_vrs_with_old_vrs_of_n_to_pending_scale_down_req_in_flight(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    n > 0
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, old_vrs_list_len(n))]),
            no_pending_req_in_cluster(vd, controller_id),
            with_n_old_vrs_in_etcd(controller_id, vd, n),
            local_state_match_etcd_on_old_vrs_list(vd, controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, old_vrs_list_len(n - nat1!()))]),
            pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, int0!()),
            with_n_old_vrs_in_etcd(controller_id, vd, n),
            local_state_match_etcd_on_old_vrs_list(vd, controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, old_vrs_list_len(n))]),
        no_pending_req_in_cluster(vd, controller_id),
        with_n_old_vrs_in_etcd(controller_id, vd, n),
        local_state_match_etcd_on_old_vrs_list(vd, controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, old_vrs_list_len(n - nat1!()))]),
        pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, int0!()),
        with_n_old_vrs_in_etcd(controller_id, vd, n),
        local_state_match_etcd_on_old_vrs_list(vd, controller_id)
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
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input.get_Some_0();
                lemma_api_request_other_than_pending_req_msg_maintains_filter_old_and_new_vrs_on_etcd(
                    s, s_prime, vd, cluster, controller_id, msg
                );
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == None::<Message> && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    // the request should carry the update of replicas, which requires reasoning over unmarshalling vrs
                    VReplicaSetView::marshal_preserves_integrity();
                    let vds = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
                    let vds_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
                    commutativity_of_seq_drop_last_and_map(vds.old_vrs_list, |vrs: VReplicaSetView| vrs.object_ref());
                }
            },
            _ => {}
        }
    }
    // without this proof will fail
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime)  by {
        VDeploymentReconcileState::marshal_preserves_integrity();
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

pub proof fn lemma_from_old_vrs_len_zero_at_scale_down_old_vrs_to_current_state_matches(
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
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, old_vrs_list_len(nat0!()))]),
            resp_msg_is_scale_down_old_vrs_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
            with_n_old_vrs_in_etcd(controller_id, vd, nat0!())
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![Done]),
            current_state_matches(vd)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, old_vrs_list_len(nat0!()))]),
        resp_msg_is_scale_down_old_vrs_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
        with_n_old_vrs_in_etcd(controller_id, vd, nat0!())
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Done]),
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
                let msg = input.get_Some_0();
                lemma_api_request_other_than_pending_req_msg_maintains_filter_old_and_new_vrs_on_etcd(
                    s, s_prime, vd, cluster, controller_id, msg
                );
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == Some(resp_msg) && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                }
            },
            _ => {}
        }
    }
    // without this the proof will be 1s slower
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime)  by {
        VDeploymentReconcileState::marshal_preserves_integrity();
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

pub proof fn lemma_from_old_vrs_len_zero_at_after_ensure_new_vrs_to_current_state_matches(
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
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, old_vrs_list_len(nat0!()))]),
            no_pending_req_in_cluster(vd, controller_id),
            with_n_old_vrs_in_etcd(controller_id, vd, nat0!())
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step!(Done)),
            current_state_matches(vd)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, old_vrs_list_len(nat0!()))]),
        no_pending_req_in_cluster(vd, controller_id),
        with_n_old_vrs_in_etcd(controller_id, vd, nat0!())
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Done]),
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
    let input = (None, Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input.get_Some_0();
                lemma_api_request_other_than_pending_req_msg_maintains_filter_old_and_new_vrs_on_etcd(
                    s, s_prime, vd, cluster, controller_id, msg
                );
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == None::<Message> && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                }
            },
            _ => {}
        }
    }
    // without this proof will fail
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime)  by {
        VDeploymentReconcileState::marshal_preserves_integrity();
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
    spec.entails(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or![AfterListVRS]), req_msg_is_the_pending_list_req_in_flight(vd, controller_id, req_msg)))
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or![AfterListVRS]), exists_pending_list_resp_in_flight_and_match_req(vd, controller_id))))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or![AfterListVRS]),
        req_msg_is_the_pending_list_req_in_flight(vd, controller_id, req_msg)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or![AfterListVRS]),
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
    spec.entails(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or![Init]), no_pending_req_in_cluster(vd, controller_id)))
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or![AfterListVRS]), pending_list_req_in_flight(vd, controller_id))))),
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or![Init]),
        no_pending_req_in_cluster(vd, controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or![AfterListVRS]),
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