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
    spec.entails(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step![Init]), no_pending_req_in_cluster(vd, controller_id)))
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step![Done]), current_state_matches(vd))))),
{
    let inv = {
        &&& spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))))
        &&& spec.entails(always(lift_action(cluster.next())))
        &&& spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i)))
        &&& spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1))))
    };
    // Init ~> send list req
    let init = lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step![Init]), no_pending_req_in_cluster(vd, controller_id)));
    let list_req = lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]), pending_list_req_in_flight(vd, controller_id)));
    assert(spec.entails(init.leads_to(list_req))) by {
        lemma_from_init_step_to_send_list_vrs_req(vd, spec, cluster, controller_id);
    }
    // send list req ~> exists |msg| list_req_msg(msg)
    // TODO: try to use X_req == tla_exists(|msg| X_req_msg(msg)) in the future
    let list_req_msg = |msg| lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]), req_msg_is_pending_list_req_in_flight(vd, controller_id, msg)));
    // list_req |= \E |msg| list_req_msg(msg)
    assert(spec.entails(list_req.leads_to(tla_exists(|msg| list_req_msg(msg))))) by {
        assert forall |ex| #[trigger] list_req.satisfied_by(ex) implies
            tla_exists(|msg| list_req_msg(msg)).satisfied_by(ex) by {
            let req_msg = ex.head().ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0();
            tla_exists_proved_by_witness(ex, |msg| list_req_msg(msg), req_msg);
        }
        // |= |= ~>
        entails_implies_leads_to(spec, list_req, tla_exists(|msg| list_req_msg(msg)));
    }
    let list_resp = lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        exists_pending_list_resp_in_flight_and_match_req(vd, controller_id)
    ));
    // \A |msg| (list_req_msg(msg) ~> list_resp)
    assert forall |req_msg: Message| inv implies #[trigger] spec.entails(list_req_msg(req_msg).leads_to(list_resp)) by {
        lemma_from_after_send_list_vrs_req_to_receive_list_vrs_resp(vd, spec, cluster, controller_id, req_msg);
    };
    // \A |msg| (list_req_msg(msg) ~> list_resp) |= (\E |msg| list_resp_msg(msg)) ~> list_resp
    leads_to_exists_intro(spec, |req_msg| list_req_msg(req_msg), list_resp);
    let list_resp_msg = |msg| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, msg)
    ));
    // list_resp ~> \E |msg| list_resp_msg(msg)
    assert(spec.entails(list_resp.leads_to(tla_exists(|msg| list_resp_msg(msg))))) by {
        // list_resp |= \E |msg| list_resp_msg(msg)
        assert forall |ex| #[trigger] list_resp.satisfied_by(ex) implies
            tla_exists(|msg| list_resp_msg(msg)).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0();
            let resp_msg = choose |resp_msg| {
                &&& #[trigger] s.in_flight().contains(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& resp_msg_is_ok_list_resp_containing_matched_vrs(s, vd, resp_msg)
            };
            tla_exists_proved_by_witness(ex, |msg| list_resp_msg(msg), resp_msg);
        }
        // |= |= ~>
        entails_implies_leads_to(spec, list_resp, tla_exists(|msg| list_resp_msg(msg)));
    };
    let after_list_with_etcd_state = |msg: Message, replicas_or_not_exist: Option<int>, n: nat| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, msg),
        etcd_state_is(vd, controller_id, replicas_or_not_exist, n)
    ));
    let after_ensure_vrs = |n: nat| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
    ));
    // from list_resp with different etcd state to different transitions to AfterEnsureNewVRS
    // \A |msg| (list_resp_msg(msg) ~> \E |n: nat| after_ensure_vrs(n))
    assert forall |msg: Message| #![trigger list_resp_msg(msg)] spec.entails(list_resp_msg(msg).leads_to(tla_exists(|n: nat| after_ensure_vrs(n)))) by{
        // (\A |msg|) list_resp_msg(msg) |= \E |replicas: Options<int>, n: nat| after_ensure_vrs(n)
        // here replicas.is_Some == if new vrs exists, replicas.get_Some_0() == new_vrs.spec.replicas.unwrap_or(1)
        // 1 is the default value if not set
        assert(list_resp_msg(msg).entails(tla_exists(|i: (Option<int>, nat)| after_list_with_etcd_state(msg, i.0, i.1)))) by {
            assert forall |ex: Execution<ClusterState>| #[trigger] list_resp_msg(msg).satisfied_by(ex) implies
                tla_exists(|i: (Option<int>, nat)| after_list_with_etcd_state(msg, i.0, i.1)).satisfied_by(ex) by {
                let s = ex.head();
                let (new_vrs, old_vrs_list) = filter_old_and_new_vrs_on_etcd(vd, s.resources());
                let replicas = if new_vrs.is_Some() {
                    Some(new_vrs.get_Some_0().spec.replicas.unwrap_or(int1!()))
                } else {
                    None
                };
                let n = old_vrs_list.len();
                // let (replicas_or_not_exist, n) = choose |i: (Option<int>, nat)| #[trigger] etcd_state_is(vd, controller_id, i.0, i.1)(s);
                tla_exists_proved_by_witness(ex, |i: (Option<int>, nat)| after_list_with_etcd_state(msg, i.0, i.1), (replicas, n));
            }
        }
        entails_implies_leads_to(spec, list_resp_msg(msg), tla_exists(|i: (Option<int>, nat)| after_list_with_etcd_state(msg, i.0, i.1)));
        // \A |n| \A |replicas| etcd_state_is(replicas, n) ~> after_ensure_vrs(n)
        assert forall |n: nat| #![trigger after_ensure_vrs(n)] spec.entails(tla_exists(|replicas: Option<int>| after_list_with_etcd_state(msg, replicas, n)).leads_to(after_ensure_vrs(n))) by {
            // \A |replicas| after_list_with_etcd_state(msg, Some(replicas), n) ~> after_ensure_vrs(n)
            // since here the transitions branch over the existence and replicas of new vrs
            assert forall |replicas: Option<int>| spec.entails(#[trigger] after_list_with_etcd_state(msg, replicas, n).leads_to(after_ensure_vrs(n))) by {
                // new vrs does not exists. Here the existance is encoded as is_Some, and replicas is get_Some_0
                if replicas.is_None() {
                    // AfterListVRS ~> AfterCreateNewVRS
                    let create_vrs_req = lift_state(and!(
                        at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
                        pending_create_new_vrs_req_in_flight(vd, controller_id),
                        etcd_state_is(vd, controller_id, None, n),
                        local_state_match_etcd(vd, controller_id)
                    ));
                    assert(spec.entails(after_list_with_etcd_state(msg, None, n).leads_to(create_vrs_req))) by {
                        lemma_from_after_receive_list_vrs_resp_to_send_create_new_vrs_req(vd, spec, cluster, controller_id, msg, n);
                    }
                    let create_vrs_req_msg = |msg: Message| lift_state(and!(
                        at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
                        req_msg_is_pending_create_new_vrs_req_in_flight(vd, controller_id, msg),
                        etcd_state_is(vd, controller_id, None, n),
                        local_state_match_etcd(vd, controller_id)
                    ));
                    assert(spec.entails(create_vrs_req.leads_to(tla_exists(|msg| create_vrs_req_msg(msg))))) by {
                        assert forall |ex: Execution<ClusterState>| #![trigger dummy(ex)] create_vrs_req.satisfied_by(ex) implies
                            tla_exists(|msg| create_vrs_req_msg(msg)).satisfied_by(ex) by {
                            let s = ex.head();
                            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0();
                            tla_exists_proved_by_witness(ex, |msg| create_vrs_req_msg(msg), req_msg);
                        }
                        entails_implies_leads_to(spec, create_vrs_req, tla_exists(|msg| create_vrs_req_msg(msg)));
                    }
                    let create_vrs_resp = lift_state(and!(
                        at_vd_step_with_vd(vd, controller_id, at_step![(AfterCreateNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
                        exists_resp_msg_is_ok_create_new_vrs_resp(vd, controller_id),
                        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
                        local_state_match_etcd(vd, controller_id)
                    ));
                    assert forall |msg: Message| #![trigger dummy(msg)] spec.entails(create_vrs_req_msg(msg).leads_to(create_vrs_resp)) by {
                        lemma_from_after_send_create_pod_req_to_receive_ok_resp(vd, spec, cluster, controller_id, msg, n);
                    }
                    leads_to_exists_intro(spec, |msg| create_vrs_req_msg(msg), create_vrs_resp);
                    let create_vrs_resp_msg = |msg: Message| lift_state(and!(
                        at_vd_step_with_vd(vd, controller_id, at_step![(AfterCreateNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
                        resp_msg_is_ok_create_new_vrs_resp(vd, controller_id, msg),
                        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
                        local_state_match_etcd(vd, controller_id)
                    ));
                    // TODO: fix this
                    assert(spec.entails(create_vrs_resp.leads_to(tla_exists(|msg| create_vrs_resp_msg(msg))))) by {
                        assume(false);
                        assert forall |ex: Execution<ClusterState>| #![trigger dummy(ex)] create_vrs_resp.satisfied_by(ex) implies
                            tla_exists(|msg| create_vrs_resp_msg(msg)).satisfied_by(ex) by {
                            let s = ex.head();
                            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0();
                            let resp_msg = choose |resp_msg| {
                                &&& #[trigger] s.in_flight().contains(resp_msg)
                                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                                &&& resp_msg.content.is_create_response()
                                &&& resp_msg.content.get_create_response().res.is_Ok()
                            };
                            tla_exists_proved_by_witness(ex, |msg| create_vrs_resp_msg(msg), resp_msg);
                        }
                        entails_implies_leads_to(spec, create_vrs_resp, tla_exists(|msg| create_vrs_resp_msg(msg)));
                    }
                    // AfterCreateNewVRS ~> AfterEnsureNewVRS
                    // Because maxSurge is not supported, this transition can be completed without scaling new VRS
                    assert forall |msg: Message| #![trigger dummy(msg)] spec.entails(create_vrs_resp_msg(msg).leads_to(after_ensure_vrs(n))) by {
                        lemma_from_receive_ok_resp_after_create_new_vrs_to_after_ensure_new_vrs(vd, spec, cluster, controller_id, msg, n);
                    }
                    // TODO: fix this
                    // leads_to_exists_intro(spec, |msg| create_vrs_resp_msg(msg), after_ensure_vrs(n));
                    assume(spec.entails(tla_exists(|msg| create_vrs_resp_msg(msg)).leads_to(after_ensure_vrs(n))));
                    leads_to_trans_n!(
                        spec,
                        after_list_with_etcd_state(msg, replicas, n),
                        create_vrs_req,
                        tla_exists(|msg| create_vrs_req_msg(msg)),
                        create_vrs_resp,
                        tla_exists(|msg| create_vrs_resp_msg(msg)),
                        after_ensure_vrs(n)
                    );
                } else {
                    if replicas.unwrap_or(1) != vd.spec.replicas.unwrap_or(1) {
                        let scale_new_vrs_req = lift_state(and!(
                            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
                            pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, vd.spec.replicas.unwrap_or(int1!())),
                            etcd_state_is(vd, controller_id, replicas, n),
                            local_state_match_etcd(vd, controller_id)
                        ));
                        assert(spec.entails(after_list_with_etcd_state(msg, replicas, n).leads_to(scale_new_vrs_req))) by {
                            lemma_from_after_receive_list_vrs_resp_to_pending_scale_new_vrs_req_in_flight(vd, spec, cluster, controller_id, msg, replicas.unwrap_or(int1!()), n);
                        }
                        let scale_new_vrs_req_msg = |msg: Message| lift_state(and!(
                            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
                            req_msg_is_pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, msg, vd.spec.replicas.unwrap_or(int1!())),
                            etcd_state_is(vd, controller_id, replicas, n),
                            local_state_match_etcd(vd, controller_id)
                        ));
                        // TODO: fix this
                        // temp_pred_equality(scale_new_vrs_req, tla_exists(|msg| scale_new_vrs_req_msg(msg)));
                        assert(scale_new_vrs_req.entails(tla_exists(|msg| scale_new_vrs_req_msg(msg)))) by {
                            assume(false);
                            assert forall |ex: Execution<ClusterState>| #![trigger dummy(ex)] scale_new_vrs_req.satisfied_by(ex) implies
                                tla_exists(|msg| scale_new_vrs_req_msg(msg)).satisfied_by(ex) by {
                                let s = ex.head();
                                let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0();
                                tla_exists_proved_by_witness(ex, |msg| scale_new_vrs_req_msg(msg), req_msg);
                            }
                        }
                        entails_implies_leads_to(spec, scale_new_vrs_req, tla_exists(|msg| scale_new_vrs_req_msg(msg)));
                        let scale_new_vrs_resp = lift_state(and!(
                            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
                            exists_resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, vd.spec.replicas.unwrap_or(int1!())),
                            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
                            local_state_match_etcd(vd, controller_id)
                        ));
                        assert forall |msg: Message| spec.entails(#[trigger] scale_new_vrs_req_msg(msg).leads_to(scale_new_vrs_resp)) by {
                            lemma_from_after_send_get_then_update_req_to_receive_ok_resp_of_new_replicas(vd, spec, cluster, controller_id, msg, replicas.unwrap_or(int1!()), n);
                        }
                        leads_to_exists_intro(spec, |msg| scale_new_vrs_req_msg(msg), scale_new_vrs_resp);
                        let scale_new_vrs_resp_msg = |msg: Message| lift_state(and!(
                            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
                            resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, msg, vd.spec.replicas.unwrap_or(int1!())),
                            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
                            local_state_match_etcd(vd, controller_id)
                        ));
                        assert(scale_new_vrs_resp.entails(tla_exists(|msg| scale_new_vrs_resp_msg(msg)))) by {
                            assume(false);
                            assert forall |ex: Execution<ClusterState>| #![trigger dummy(ex)] scale_new_vrs_resp.satisfied_by(ex) implies
                                tla_exists(|msg| scale_new_vrs_resp_msg(msg)).satisfied_by(ex) by {
                                assume(false);
                                let s = ex.head();
                                let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0();
                                let resp_msg = choose |resp_msg| {
                                    &&& #[trigger] s.in_flight().contains(resp_msg)
                                    &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                                    &&& resp_msg.content.is_get_then_update_response()
                                    &&& resp_msg.content.get_get_then_update_response().res.is_Ok()
                                };
                                tla_exists_proved_by_witness(ex, |msg| scale_new_vrs_resp_msg(msg), resp_msg);
                            }
                        }
                        entails_implies_leads_to(spec, scale_new_vrs_resp, tla_exists(|msg| scale_new_vrs_resp_msg(msg)));
                        assert forall |msg: Message| spec.entails(#[trigger] scale_new_vrs_resp_msg(msg).leads_to(after_ensure_vrs(n))) by {
                            lemma_from_receive_ok_resp_after_scale_new_vrs_to_after_ensure_new_vrs(vd, spec, cluster, controller_id, msg, n);
                        }
                        leads_to_exists_intro(spec, |msg| scale_new_vrs_resp_msg(msg), after_ensure_vrs(n));
                        leads_to_trans_n!(
                            spec,
                            after_list_with_etcd_state(msg, replicas, n),
                            scale_new_vrs_req,
                            tla_exists(|msg| scale_new_vrs_req_msg(msg)),
                            scale_new_vrs_resp,
                            tla_exists(|msg| scale_new_vrs_resp_msg(msg)),
                            after_ensure_vrs(n)
                        );
                    } else {
                        lemma_from_after_receive_list_vrs_resp_to_after_ensure_new_vrs(vd, spec, cluster, controller_id, msg, replicas.unwrap_or(1), n);
                    }
                }
            }
            leads_to_exists_intro(spec, |replicas: Option<int>| after_list_with_etcd_state(msg, replicas, n), after_ensure_vrs(n));
        }
        // need to prove (\A |a| (a_to_p(a) ~> a_to_q(a))) && (r ~> \E |a| a_to_p(a)) ==> r ~> \E |a| a_to_q(a)
        assert(spec.entails(tla_exists(|i: (Option<int>, nat)| after_list_with_etcd_state(msg, i.0, i.1)).leads_to(tla_exists(|n: nat| after_ensure_vrs(n))))) by {
            assume(false);
        };
        // no proper trigger inside tla_exists, if I use dummy I will make verus panic
        // assert(tla_exists(|i: (Option<int>, nat)| after_list_with_etcd_state(msg, i.0, i.1)).entails(tla_exists(|n: nat| tla_exists(|replicas: Option<int>| after_list_with_etcd_state(msg, replicas, n))))) by {
        //     assume(false);
        //     assert forall |ex: Execution<ClusterState>| tla_exists(|i: (Option<int>, nat)| after_list_with_etcd_state(msg, i.0, i.1)).satisfied_by(ex) implies
        //         tla_exists(|n: nat| tla_exists(|replicas: Option<int>| after_list_with_etcd_state(msg, replicas, n))).satisfied_by(ex) by {
        //         let i = tla_exists_choose_witness(ex, |i: (Option<int>, nat)| after_list_with_etcd_state(msg, i.0, i.1));
        //     }
        // }
        // temp_pred_equality(
        //     tla_exists(|n: nat| tla_exists(|replicas: Option<int>| after_list_with_etcd_state(msg, replicas, n))),
        //     tla_exists(|i: (Option<int>, nat)| after_list_with_etcd_state(msg, i.0, i.1))
        // );
        leads_to_trans_n!(
            spec,
            list_resp_msg(msg),
            tla_exists(|i: (Option<int>, nat)| after_list_with_etcd_state(msg, i.0, i.1)),
            tla_exists(|n: nat| after_ensure_vrs(n))
        );
    }
    leads_to_exists_intro(spec, |msg| list_resp_msg(msg), tla_exists(|n: nat| after_ensure_vrs(n)));
    leads_to_trans_n!(
        spec,
        init,
        list_req,
        tla_exists(|msg| list_req_msg(msg)),
        list_resp,
        tla_exists(|msg| list_resp_msg(msg)),
        tla_exists(|n| after_ensure_vrs(n))
    );
    let done = lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Done]),
        current_state_matches(vd)
    ));
    // AfterEnsureNewVRS ~> Done
    assert forall |n: nat| spec.entails(#[trigger] after_ensure_vrs(n).leads_to(done)) by {
        if n == 0 {
            // direct transition
            lemma_from_old_vrs_len_zero_after_ensure_new_vrs_to_current_state_matches(vd, spec, cluster, controller_id, n);
        } else {
            // send scale down req
            let scale_down_req = lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n - nat1!()))]),
                pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, int0!()),
                etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
                local_state_match_etcd(vd, controller_id)
            ));
            assert(spec.entails(after_ensure_vrs(n).leads_to(scale_down_req))) by {
                lemma_from_after_ensure_new_vrs_with_old_vrs_of_n_to_pending_scale_down_req_in_flight(vd, spec, cluster, controller_id, n);
            }
            let scale_down_req_msg = |msg: Message| lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n - nat1!()))]),
                req_msg_is_pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, msg, int0!()),
                etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
                local_state_match_etcd(vd, controller_id)
            ));
            assert(spec.entails(scale_down_req.leads_to(tla_exists(|msg| scale_down_req_msg(msg))))) by {
                assert forall |ex: Execution<ClusterState>| #[trigger] scale_down_req.satisfied_by(ex) implies
                    tla_exists(|msg| scale_down_req_msg(msg)).satisfied_by(ex) by {
                    let s = ex.head();
                    let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0();
                    tla_exists_proved_by_witness(ex, |msg| scale_down_req_msg(msg), req_msg);
                }
                entails_implies_leads_to(spec, scale_down_req, tla_exists(|msg| scale_down_req_msg(msg)));
            }
            // from req to resp
            let scale_down_resp = |n: nat| lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
                exists_resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, int0!()),
                etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
                local_state_match_etcd(vd, controller_id)
            ));
            // from n old vrs to scale down to n - 1 old vrs
            assert forall |msg: Message| spec.entails(#[trigger] scale_down_req_msg(msg).leads_to(scale_down_resp((n - nat1!()) as nat))) by {
                lemma_from_after_send_get_then_update_req_to_receive_get_then_update_resp_on_old_vrs_of_n(vd, spec, cluster, controller_id, msg, n);
            }
            leads_to_exists_intro(spec, |msg| scale_down_req_msg(msg), scale_down_resp((n - nat1!()) as nat));
            assert forall |n: nat| #![trigger scale_down_resp(n)] n > 0 implies spec.entails(scale_down_resp(n).leads_to(scale_down_resp((n - nat1!()) as nat))) by {
                lemma_from_n_to_n_minus_one_on_old_vrs_len(vd, spec, cluster, controller_id, n);
            }
            // n ~> n-1 ~..> 0
            assert(spec.entails(scale_down_resp((n - nat1!()) as nat).leads_to(scale_down_resp(nat0!())))) by {
                leads_to_rank_step_one(spec, scale_down_resp);
            }
            // 0 ~> Done
            let scale_down_resp_msg_zero = |msg: Message| lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), nat0!()))]),
                resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, msg, int0!()),
                etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), nat0!()),
                local_state_match_etcd(vd, controller_id)
            ));
            assert(scale_down_resp(nat0!()).entails(tla_exists(|msg| scale_down_resp_msg_zero(msg)))) by {
                assert forall |ex: Execution<ClusterState>| #[trigger] scale_down_resp(nat0!()).satisfied_by(ex) implies
                    tla_exists(|msg| scale_down_resp_msg_zero(msg)).satisfied_by(ex) by {
                    let s = ex.head();
                    let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0();
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] s.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.is_get_then_update_response()
                        &&& resp_msg.content.get_get_then_update_response().res.is_Ok()
                    };
                    tla_exists_proved_by_witness(ex, |msg| scale_down_resp_msg_zero(msg), resp_msg);
                }
            }
            entails_implies_leads_to(spec, scale_down_resp(nat0!()), tla_exists(|msg| scale_down_resp_msg_zero(msg)));
            assert forall |msg: Message| spec.entails(#[trigger] scale_down_resp_msg_zero(msg).leads_to(done)) by {
                lemma_from_old_vrs_len_zero_at_scale_down_old_vrs_to_current_state_matches(vd, spec, cluster, controller_id, msg);
            }
            leads_to_exists_intro(spec, |msg| scale_down_resp_msg_zero(msg), done);
            leads_to_trans_n!(
                spec,
                after_ensure_vrs(n),
                scale_down_req,
                tla_exists(|msg| scale_down_req_msg(msg)),
                scale_down_resp((n - nat1!()) as nat),
                scale_down_resp(nat0!()),
                tla_exists(|msg| scale_down_resp_msg_zero(msg)),
                done
            );
        }
    }
    leads_to_exists_intro(spec, |n: nat| after_ensure_vrs(n), done);
    leads_to_trans_n!(
        spec,
        init,
        tla_exists(|n| after_ensure_vrs(n)),
        done
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
    spec.entails(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step![Init]), no_pending_req_in_cluster(vd, controller_id)))
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]), pending_list_req_in_flight(vd, controller_id))))),
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
    // this assertion makes proof 86% faster
    assert(forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) ==> pre(s_prime) || post(s_prime));
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
    spec.entails(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]), req_msg_is_pending_list_req_in_flight(vd, controller_id, req_msg)))
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]), exists_pending_list_resp_in_flight_and_match_req(vd, controller_id))))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        req_msg_is_pending_list_req_in_flight(vd, controller_id, req_msg)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
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

#[verifier(spinoff_prover)]
pub proof fn lemma_from_after_receive_list_vrs_resp_to_after_ensure_new_vrs(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message, replicas: int, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    replicas == vd.spec.replicas.unwrap_or(int1!()),
ensures
    spec.entails(lift_state(and!(
            // at this stage there's no local cache available
            at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
            resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
            etcd_state_is(vd, controller_id, Some(replicas), n)
        ))
        .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
            no_pending_req_in_cluster(vd, controller_id),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
            local_state_match_etcd(vd, controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
        etcd_state_is(vd, controller_id, Some(replicas), n)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
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
                assume(false);
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == Some(resp_msg) && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    VReplicaSetView::marshal_preserves_integrity();
                    let vrls = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
                    let vrls_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
                    assert((vrls_prime.new_vrs, vrls_prime.old_vrs_list) == filter_old_and_new_vrs_on_etcd(vd, s.resources())) by {
                        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                        let vrs_list_or_none = objects_to_vrs_list(resp_objs);
                        assert(resp_msg.content.is_list_response());
                        assert(resp_msg.content.get_list_response().res.is_Ok());
                        assert(vrs_list_or_none.is_Some());
                        assert(resp_objs == s.resources().values().filter(list_vrs_obj_filter(vd)).to_seq());
                        assert(filter_old_and_new_vrs(vd, filter_vrs_list(vd, vrs_list_or_none.get_Some_0())) == filter_old_and_new_vrs_on_etcd(vd, s.resources()));
                        let (new_vrs_or_none, old_vrs_list) = filter_old_and_new_vrs(vd, filter_vrs_list(vd, vrs_list_or_none.get_Some_0()));
                        assert(new_vrs_or_none.is_Some());
                        let new_vrs = new_vrs_or_none.get_Some_0();
                        assert(match_replicas(vd, new_vrs));
                        assert(vrls_prime.new_vrs.is_Some());
                        assert(vrls_prime.new_vrs.get_Some_0() == new_vrs);
                        assert(vrls_prime.old_vrs_list == old_vrs_list);
                        assert(vrls_prime.reconcile_step == AfterEnsureNewVRS);
                        // maybe another flaky case
                        // if I use assert(vrls_prime == VDeploymentReconcileState{..}) I get
//                      vrls_prime == VDeploymentReconcileState { new_vrs: Some(new_vrs), old_vrs_list: old_vrs_list, reconcile_step: AfterCreateNewVRS }
//                      |   vrls_prime.reconcile_step == AfterCreateNewVRS ✘
//                      |   |   !(vrls_prime.reconcile_step is Init) ✔
//                      |   |   !(vrls_prime.reconcile_step is AfterListVRS) ✔
//                      |   |   !(vrls_prime.reconcile_step is AfterScaleNewVRS) ✘
//                      |   |   !(vrls_prime.reconcile_step is AfterEnsureNewVRS) ✘
//                      |   |   !(vrls_prime.reconcile_step is AfterScaleDownOldVRS) ✔
//                      |   |   !(vrls_prime.reconcile_step is Done) ✔
//                      |   |   !(vrls_prime.reconcile_step is Error) ✔
//                      |   +---
//                      |   vrls_prime.new_vrs == Some(new_vrs) ✘
//                      |   |   !(vrls_prime.new_vrs is None) ✔
//                      |   |   vrls_prime.new_vrs is Some ==>
//                      |   |       vrls_prime.new_vrs.0 == new_vrs ✘
//                      |   |       |   vrls_prime.new_vrs.0.metadata == new_vrs.metadata ✘
//                      |   |       |   |   vrls_prime.new_vrs.0.metadata.name == new_vrs.metadata.name ✘
//                      |   |       |   |   |   vrls_prime.new_vrs.0.metadata.name is None ==>
//                      |   |       |   |   |       new_vrs.metadata.name is None ✔
//                      |   |       |   |   |   vrls_prime.new_vrs.0.metadata.name is Some ==>
//                      |   |       |   |   |       new_vrs.metadata.name is Some ✘
//                      |   |       |   |   |       vrls_prime.new_vrs.0.metadata.name.0 == new_vrs.metadata.name.0 ✘
//                      |   |       |   |   |           datatype is opaque here
                        // if I use vrls_prime.new_vrs == Some(new_vrs) I get
                        // !(vrls_prime.new_vrs is None) ✘
                    }
                }
            },
            _ => {}
        }
    }
    assume(false);
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        VDeploymentReconcileState::marshal_preserves_integrity();
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

// maybe another case of flakiness, see verus log
pub proof fn lemma_from_after_receive_list_vrs_resp_to_send_create_new_vrs_req(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
            resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
            etcd_state_is(vd, controller_id, None, n)
        ))
        .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
            pending_create_new_vrs_req_in_flight(vd, controller_id),
            etcd_state_is(vd, controller_id, None, n),
            local_state_match_etcd(vd, controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
        etcd_state_is(vd, controller_id, None, n)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        pending_create_new_vrs_req_in_flight(vd, controller_id),
        etcd_state_is(vd, controller_id, None, n),
        local_state_match_etcd(vd, controller_id)
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
                    // the request should carry the make_replica_set(vd).marshal(), which requires reasoning over unmarshalling vrs
                    VReplicaSetView::marshal_preserves_integrity();
                    let vrls = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
                    let vrls_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
                    assert((vrls_prime.new_vrs, vrls_prime.old_vrs_list) == filter_old_and_new_vrs_on_etcd(vd, s.resources())) by {
                        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                        let vrs_list_or_none = objects_to_vrs_list(resp_objs);
                        assert(resp_msg.content.is_list_response());
                        assert(resp_msg.content.get_list_response().res.is_Ok());
                        assert(vrs_list_or_none.is_Some());
                        assert(resp_objs == s.resources().values().filter(list_vrs_obj_filter(vd)).to_seq());
                        assert(filter_old_and_new_vrs(vd, filter_vrs_list(vd, vrs_list_or_none.get_Some_0())) == filter_old_and_new_vrs_on_etcd(vd, s.resources()));
                        let (new_vrs_or_none, old_vrs_list) = filter_old_and_new_vrs(vd, filter_vrs_list(vd, vrs_list_or_none.get_Some_0()));
                        assert(new_vrs_or_none.is_None());
                        // try comment out the next line
                        assert(vrls_prime.new_vrs == Some(make_replica_set(vd)));
                        assert(vrls_prime == create_new_vrs(old_vrs_list, vd).0);
                    }
                }
            },
            _ => {}
        }
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

pub proof fn lemma_from_after_send_create_pod_req_to_receive_ok_resp(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, req_msg: Message, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterListVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
            req_msg_is_pending_create_new_vrs_req_in_flight(vd, controller_id, req_msg),
            etcd_state_is(vd, controller_id, None, n),
            local_state_match_etcd(vd, controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterCreateNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
            exists_resp_msg_is_ok_create_new_vrs_resp(vd, controller_id),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
            local_state_match_etcd(vd, controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterListVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        req_msg_is_pending_create_new_vrs_req_in_flight(vd, controller_id, req_msg),
        etcd_state_is(vd, controller_id, None, n),
        local_state_match_etcd(vd, controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterCreateNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        exists_resp_msg_is_ok_create_new_vrs_resp(vd, controller_id),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
    };
    let input = Some(req_msg);
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
                    let resp_msg = lemma_create_new_vrs_request_returns_ok_after_ensure_new_vrs(
                        s, s_prime, vd, cluster, controller_id, msg, n
                    );
                    VReplicaSetView::marshal_preserves_integrity();
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                    });
                }
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let msg = input.get_Some_0();
        let resp_msg = lemma_create_new_vrs_request_returns_ok_after_ensure_new_vrs(
            s, s_prime, vd, cluster, controller_id, msg, n
        );
        // instantiate existential quantifier.
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
        });
    }
    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

#[verifier(external_body)]
// need a step from exists to instantitated resp
pub proof fn lemma_from_receive_ok_resp_after_create_new_vrs_to_after_ensure_new_vrs(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterCreateNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
            resp_msg_is_ok_create_new_vrs_resp(vd, controller_id, resp_msg),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
            local_state_match_etcd(vd, controller_id)
        ))
        .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
            no_pending_req_in_cluster(vd, controller_id),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
            local_state_match_etcd(vd, controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterCreateNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        resp_msg_is_ok_create_new_vrs_resp(vd, controller_id, resp_msg),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
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
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        VDeploymentReconcileState::marshal_preserves_integrity();
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

#[verifier(external_body)]
pub proof fn lemma_from_after_receive_list_vrs_resp_to_pending_scale_new_vrs_req_in_flight(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message, replicas: int, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    replicas != vd.spec.replicas.unwrap_or(int1!()),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
            resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
            etcd_state_is(vd, controller_id, Some(replicas), n)
        ))
        .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
            pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, vd.spec.replicas.unwrap_or(int1!())),
            etcd_state_is(vd, controller_id, Some(replicas), n),
            local_state_match_etcd(vd, controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
        etcd_state_is(vd, controller_id, Some(replicas), n),
        local_state_match_etcd(vd, controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, vd.spec.replicas.unwrap_or(int1!())),
        etcd_state_is(vd, controller_id, Some(replicas), n),
        local_state_match_etcd(vd, controller_id)
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
                    // the request should carry the update of replicas, which requires reasoning over unmarshalling vrs
                    VReplicaSetView::marshal_preserves_integrity();
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

#[verifier(external_body)]
pub proof fn lemma_from_after_send_get_then_update_req_to_receive_ok_resp_of_new_replicas(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, req_msg: Message, replicas: int, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
            req_msg_is_pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, req_msg, vd.spec.replicas.unwrap_or(int1!())),
            etcd_state_is(vd, controller_id, Some(replicas), n),
            local_state_match_etcd(vd, controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
            exists_resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, vd.spec.replicas.unwrap_or(int1!())),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
            local_state_match_etcd(vd, controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        req_msg_is_pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, req_msg, vd.spec.replicas.unwrap_or(int1!())),
        etcd_state_is(vd, controller_id, Some(replicas), n),
        local_state_match_etcd(vd, controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        exists_resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, vd.spec.replicas.unwrap_or(int1!())),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
    };
    let input = Some(req_msg);
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
                    let resp_msg = lemma_get_then_update_request_returns_ok_after_scale_new_vrs(
                        s, s_prime, vd, cluster, controller_id, msg, replicas, n
                    );
                    VReplicaSetView::marshal_preserves_integrity();
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                    });
                }
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let msg = input.get_Some_0();
        let resp_msg = lemma_get_then_update_request_returns_ok_after_scale_new_vrs(
            s, s_prime, vd, cluster, controller_id, msg, replicas, n
        );
        // instantiate existential quantifier.
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
        });
    }
    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

// same as lemma_from_receive_ok_resp_after_create_new_vrs_to_after_ensure_new_vrs
#[verifier(external_body)]
pub proof fn lemma_from_receive_ok_resp_after_scale_new_vrs_to_after_ensure_new_vrs(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
            resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, resp_msg, vd.spec.replicas.unwrap_or(int1!())),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
            local_state_match_etcd(vd, controller_id)
        ))
        .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
            no_pending_req_in_cluster(vd, controller_id),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
            local_state_match_etcd(vd, controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        resp_msg_is_ok_create_new_vrs_resp(vd, controller_id, resp_msg),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
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
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        VDeploymentReconcileState::marshal_preserves_integrity();
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

#[verifier(external_body)]
pub proof fn lemma_from_after_ensure_new_vrs_with_old_vrs_of_n_to_pending_scale_down_req_in_flight(
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
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
            no_pending_req_in_cluster(vd, controller_id),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
            local_state_match_etcd(vd, controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n - nat1!()))]),
            pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, int0!()),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
            local_state_match_etcd(vd, controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n - nat1!()))]),
        pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, int0!()),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
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

#[verifier(external_body)]
pub proof fn lemma_from_after_scale_down_old_vrs_with_old_vrs_of_n_to_pending_scale_down_req_in_flight(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message, n: nat
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
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
            resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, resp_msg, int0!()),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
            local_state_match_etcd(vd, controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n - nat1!()))]),
            pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, int0!()),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
            local_state_match_etcd(vd, controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, resp_msg, int0!()),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n - nat1!()))]),
        pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, int0!()),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
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
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime)  by {
        VDeploymentReconcileState::marshal_preserves_integrity();
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

#[verifier(external_body)]
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
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n - nat1!()))]),
            req_msg_is_pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, req_msg, int0!()),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
            local_state_match_etcd(vd, controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n - nat1!()))]),
            exists_resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, int0!()),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n - nat1!()),
            local_state_match_etcd(vd, controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n - nat1!()))]),
        req_msg_is_pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, req_msg, int0!()),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n - nat1!()))]),
        exists_resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, int0!()),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n - nat1!()),
        local_state_match_etcd(vd, controller_id)
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
                    let resp_msg = lemma_get_then_update_request_returns_ok_after_scale_down_old_vrs(s, s_prime, vd, cluster, controller_id, msg, n);
                    VReplicaSetView::marshal_preserves_integrity();
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                    });
                }
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let msg = input.get_Some_0();
        let resp_msg = lemma_get_then_update_request_returns_ok_after_scale_down_old_vrs(s, s_prime, vd, cluster, controller_id, msg, n);
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

pub proof fn lemma_from_n_to_n_minus_one_on_old_vrs_len(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    n > 0
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
            exists_resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, int0!()),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
            local_state_match_etcd(vd, controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n - nat1!()))]),
            exists_resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, int0!()),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n - nat1!()),
            local_state_match_etcd(vd, controller_id)
        )))),
{
    let scale_resp = |n: nat| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        exists_resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, int0!()),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
    ));
    let scale_resp_msg = |msg: Message, n: nat| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, msg, int0!()),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
    ));
    let scale_req = |n: nat| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n - nat1!()))]),
        pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, int0!()),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
    ));
    let scale_req_msg = |msg: Message, n: nat| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n - nat1!()))]),
        req_msg_is_pending_get_then_update_req_in_flight_with_replicas(vd, controller_id, msg, int0!()),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
    ));
    assert forall |resp_msg: Message| n > 0 implies #[trigger]
        spec.entails(scale_resp_msg(resp_msg, n).leads_to(scale_req(n))) by {
        lemma_from_after_scale_down_old_vrs_with_old_vrs_of_n_to_pending_scale_down_req_in_flight(
            vd, spec, cluster, controller_id, resp_msg, n
        );
    }
    assert forall |req_msg: Message| n > 0 implies #[trigger]
        spec.entails(scale_req_msg(req_msg, n).leads_to(scale_resp((n - 1) as nat))) by {
        lemma_from_after_send_get_then_update_req_to_receive_get_then_update_resp_on_old_vrs_of_n(
            vd, spec, cluster, controller_id, req_msg, n
        );
    }
    leads_to_exists_intro(spec, |resp_msg: Message| scale_resp_msg(resp_msg, n), scale_req(n));
    leads_to_exists_intro(spec, |req_msg: Message| scale_req_msg(req_msg, n), scale_resp((n - 1) as nat));
    assert(spec.entails(scale_req(n).leads_to(tla_exists(|req_msg: Message| scale_req_msg(req_msg, n))))) by {
        assert forall |ex| #[trigger] scale_req(n).satisfied_by(ex) implies
            tla_exists(|req_msg: Message| scale_req_msg(req_msg, n)).satisfied_by(ex) by {
            let req_msg = ex.head().ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0();
            tla_exists_proved_by_witness(ex, |req_msg| scale_req_msg(req_msg, n), req_msg);
        }
        entails_implies_leads_to(spec, scale_req(n), tla_exists(|req_msg: Message| scale_req_msg(req_msg, n)));
    }
    assert(spec.entails(scale_resp(n).leads_to(tla_exists(|resp_msg: Message| scale_resp_msg(resp_msg, n))))) by {
        assert forall |ex| #[trigger] scale_resp(n).satisfied_by(ex) implies
            tla_exists(|resp_msg: Message| scale_resp_msg(resp_msg, n)).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0();
            let resp_msg = choose |resp_msg| {
                &&& #[trigger] s.in_flight().contains(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& resp_msg.content.is_get_then_update_response()
                &&& resp_msg.content.get_get_then_update_response().res.is_Ok()
            };
            tla_exists_proved_by_witness(ex, |resp_msg| scale_resp_msg(resp_msg, n), resp_msg);
        }
        entails_implies_leads_to(spec, scale_resp(n), tla_exists(|resp_msg: Message| scale_resp_msg(resp_msg, n)));
    }
    leads_to_trans_n!(spec,
        scale_resp(n),
        tla_exists(|resp_msg: Message| scale_resp_msg(resp_msg, n)),
        scale_req(n),
        tla_exists(|req_msg: Message| scale_req_msg(req_msg, n)),
        scale_resp((n - 1) as nat)
    );
}

pub proof fn lemma_from_old_vrs_len_zero_after_ensure_new_vrs_to_current_state_matches(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    n == 0,
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
            no_pending_req_in_cluster(vd, controller_id),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
            local_state_match_etcd(vd, controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step!(Done)),
            current_state_matches(vd)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterEnsureNewVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), n))]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), n),
        local_state_match_etcd(vd, controller_id)
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

#[verifier(external_body)]
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
            at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), nat0!()))]),
            resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, resp_msg, int0!()),
            etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), nat0!()),
            local_state_match_etcd(vd, controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![Done]),
            current_state_matches(vd)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![(AfterScaleDownOldVRS, local_state_is(Some(vd.spec.replicas.unwrap_or(int1!())), nat0!()))]),
        resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, resp_msg, int0!()),
        etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), nat0!())
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

}