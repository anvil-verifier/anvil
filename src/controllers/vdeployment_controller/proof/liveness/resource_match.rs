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
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use crate::reconciler::spec::io::*;
use crate::vstd_ext::{seq_lib::*, set_lib::*};
use vstd::{seq_lib::*, map_lib::*};
use vstd::prelude::*;

verus !{

pub proof fn lemma_from_init_to_current_state_matches(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id))),
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
    let list_req_msg = |msg| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        req_msg_is_pending_list_req_in_flight(vd, controller_id, msg)
    ));
    // list_req == \E |msg| list_req_msg(msg)
    assert(list_req == tla_exists(|msg| list_req_msg(msg))) by {
        assert forall |ex| #[trigger] list_req.satisfied_by(ex) implies tla_exists(|msg| list_req_msg(msg)).satisfied_by(ex) by {
            let req_msg = ex.head().ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
            assert((|msg| list_req_msg(msg))(req_msg).satisfied_by(ex));
        }
        temp_pred_equality(list_req, tla_exists(|msg| list_req_msg(msg)));
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
    // list_resp == \E |msg| list_resp_msg(msg)
    assert(list_resp == tla_exists(|msg| list_resp_msg(msg))) by {
        // list_resp |= \E |msg| list_resp_msg(msg)
        assert forall |ex| #[trigger] list_resp.satisfied_by(ex) implies
            tla_exists(|msg| list_resp_msg(msg)).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
            let resp_msg = choose |resp_msg| {
                &&& #[trigger] s.in_flight().contains(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& resp_msg_is_ok_list_resp_containing_matched_vrs(vd, controller_id, resp_msg, s)
            };
            assert((|msg| list_resp_msg(msg))(resp_msg).satisfied_by(ex));
        }
        temp_pred_equality(list_resp, tla_exists(|msg| list_resp_msg(msg)));
    };
    temp_pred_equality(list_resp, tla_exists(|msg| list_resp_msg(msg)));
    let after_list_with_etcd_state = |msg: Message, nv_uid_key_replicas: Option<(Uid, ObjectRef, int)>, n: nat| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, msg),
        etcd_state_is(vd, controller_id, nv_uid_key_replicas, n)
    ));
    let after_ensure_vrs = |i: (Uid, ObjectRef, nat)| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd, controller_id, Some((i.0, i.1, vd.spec.replicas.unwrap_or(int1!()))), i.2),
        local_state_is(vd, controller_id, Some((i.0, i.1, vd.spec.replicas.unwrap_or(int1!()))), i.2)
    ));
    // from list_resp with different etcd state to different transitions to AfterEnsureNewVRS
    // \A |msg| (list_resp_msg(msg) ~> \E |n: nat| after_ensure_vrs((nv_uid, nv_key, n)))
    assert forall |msg: Message| #![trigger list_resp_msg(msg)]
        spec.entails(list_resp_msg(msg).leads_to(tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i)))) by{
        // (\A |msg|) list_resp_msg(msg) == \E |replicas: Options<int>, n: nat| after_ensure_vrs((nv_uid, nv_key, n))
        // here replicas.is_Some == if new vrs exists, replicas->0 == new_vrs.spec.replicas.unwrap_or(int1!())
        // 1 is the default value if not set
        assert(list_resp_msg(msg) == tla_exists(|i: (Option<(Uid, ObjectRef, int)>, nat)| after_list_with_etcd_state(msg, i.0, i.1))) by {
            assert forall |ex: Execution<ClusterState>| #[trigger] list_resp_msg(msg).satisfied_by(ex) implies
                tla_exists(|i: (Option<(Uid, ObjectRef, int)>, nat)| after_list_with_etcd_state(msg, i.0, i.1)).satisfied_by(ex) by {
                let s = ex.head();
                let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
                let resp_objs = msg.content.get_list_response().res.unwrap();
                let filtered_vrs_list = objects_to_vrs_list(resp_objs).unwrap().filter(|vrs| valid_owned_vrs(vrs, triggering_cr));
                assert(filtered_vrs_list == filter_vrs_managed_by_vd(triggering_cr, s.resources()));
                let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(triggering_cr, filtered_vrs_list);
                let nv_uid_key_replicas = if new_vrs is Some {
                    let vrs = new_vrs->0;
                    Some((vrs.metadata.uid->0, vrs.object_ref(), vrs.spec.replicas.unwrap_or(int1!())))
                } else {
                    None
                };
                filtered_new_vrs_and_old_vrs_to_etcd_state_is(vd, controller_id, new_vrs, old_vrs_list, s);
                assert((|i: (Option<(Uid, ObjectRef, int)>, nat)| after_list_with_etcd_state(msg, i.0, i.1))((nv_uid_key_replicas, old_vrs_list.len())).satisfied_by(ex));
            }
            temp_pred_equality(list_resp_msg(msg), tla_exists(|i: (Option<(Uid, ObjectRef, int)>, nat)| after_list_with_etcd_state(msg, i.0, i.1)));
        }
        // \A |replicas, n| etcd_state_is(replicas, n) ~> \E |n| after_ensure_vrs((nv_uid, nv_key, n))
        assert forall |i: (Option<(Uid, ObjectRef, int)>, nat)| #![trigger after_list_with_etcd_state(msg, i.0, i.1)]
            spec.entails(after_list_with_etcd_state(msg, i.0, i.1).leads_to(tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i)))) by {
            let (nv_uid_key_replicas, n) = i;
            // new vrs does not exists. Here the existance is encoded as is_Some, and replicas is get_Some_0
            if nv_uid_key_replicas is None {
                // AfterListVRS ~> AfterCreateNewVRS
                let create_vrs_req_nv = lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
                    pending_create_new_vrs_req_in_flight(vd, controller_id),
                    etcd_state_is(vd, controller_id, None, n),
                    exists_nv_local_state_is(vd, controller_id, n)
                ));
                assert(spec.entails(after_list_with_etcd_state(msg, None, n).leads_to(create_vrs_req_nv))) by {
                    lemma_from_after_receive_list_vrs_resp_to_send_create_new_vrs_req(vd, spec, cluster, controller_id, msg, n);
                }
                let create_vrs_req = |j: (Uid, ObjectRef)| lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
                    pending_create_new_vrs_req_in_flight(vd, controller_id),
                    etcd_state_is(vd, controller_id, None, n),
                    local_state_is(vd, controller_id, Some((j.0, j.1, vd.spec.replicas.unwrap_or(int1!()))), n)
                ));
                assert(create_vrs_req_nv == tla_exists(|j: (Uid, ObjectRef)| create_vrs_req(j))) by {
                    assert forall |ex: Execution<ClusterState>| #[trigger] create_vrs_req_nv.satisfied_by(ex) implies
                        tla_exists(|j: (Uid, ObjectRef)| create_vrs_req(j)).satisfied_by(ex) by {
                        assume(false);
                        let s = ex.head();
                        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                        let vd = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
                        let request = req_msg.content.get_APIRequest_0().get_CreateRequest_0();
                        let nv = VReplicaSetView::unmarshal(request.obj)->Ok_0;
                        assert(local_state_is(vd, controller_id, Some((nv.metadata.uid->0, nv.object_ref(), vd.spec.replicas.unwrap_or(int1!()))), n)(s));
                        assert((|j: (Uid, ObjectRef)| create_vrs_req(j))((nv.metadata.uid->0, nv.object_ref())).satisfied_by(ex));
                    }
                    temp_pred_equality(create_vrs_req_nv, tla_exists(|j: (Uid, ObjectRef)| create_vrs_req(j)));
                }
                // because nv_uid_key_replicas is None, we need to instantiate them after creation
                // so we can get rid of tla_exists in this branch
                assert forall |j: (Uid, ObjectRef)| #![trigger create_vrs_req(j)] true
                    implies spec.entails(create_vrs_req(j).leads_to(tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i)))) by {
                    let (nv_uid, nv_key) = (j.0, j.1);
                    let create_vrs_req_msg = |msg: Message| lift_state(and!(
                        at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
                        req_msg_is_pending_create_new_vrs_req_in_flight(vd, controller_id, msg),
                        etcd_state_is(vd, controller_id, None, n),
                        local_state_is(vd, controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n)
                    ));
                    assert(create_vrs_req(j) == tla_exists(|msg| create_vrs_req_msg(msg))) by {
                        assert forall |ex: Execution<ClusterState>| #[trigger] create_vrs_req((nv_uid, nv_key)).satisfied_by(ex) implies
                            tla_exists(|msg| create_vrs_req_msg(msg)).satisfied_by(ex) by {
                            let s = ex.head();
                            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                            assert((|msg| create_vrs_req_msg(msg))(req_msg).satisfied_by(ex));
                        }
                        temp_pred_equality(create_vrs_req(j), tla_exists(|msg| create_vrs_req_msg(msg)));
                    }
                    let create_vrs_resp = lift_state(and!(
                        at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
                        exists_resp_msg_is_ok_create_new_vrs_resp(vd, controller_id),
                        etcd_state_is(vd, controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n),
                        local_state_is(vd, controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n)
                    ));
                    assert forall |msg: Message| spec.entails(#[trigger] create_vrs_req_msg(msg)
                        .leads_to(create_vrs_resp)) by {
                        lemma_from_after_send_create_new_vrs_req_to_receive_ok_resp(vd, spec, cluster, controller_id, msg, j, n);
                    }
                    leads_to_exists_intro(spec, |msg| create_vrs_req_msg(msg), create_vrs_resp);
                    let create_vrs_resp_msg = |msg: Message| lift_state(and!(
                        at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
                        resp_msg_is_ok_create_new_vrs_resp(vd, controller_id, msg),
                        etcd_state_is(vd, controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n),
                        local_state_is(vd, controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n)
                    ));
                    assert(create_vrs_resp == tla_exists(|msg| create_vrs_resp_msg(msg))) by {
                        assert forall |ex: Execution<ClusterState>| #[trigger] create_vrs_resp.satisfied_by(ex) implies
                            tla_exists(|msg| create_vrs_resp_msg(msg)).satisfied_by(ex) by {
                            let s = ex.head();
                            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                            let resp_msg = choose |resp_msg| {
                                &&& #[trigger] s.in_flight().contains(resp_msg)
                                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                                &&& resp_msg.content.is_create_response()
                                &&& resp_msg.content.get_create_response().res is Ok
                            };
                            // Q: how to match new_vrs in etcd and local cache?
                            assert((|msg| create_vrs_resp_msg(msg))(resp_msg).satisfied_by(ex));
                        }
                        temp_pred_equality(create_vrs_resp, tla_exists(|msg| create_vrs_resp_msg(msg)));
                    }
                    // AfterCreateNewVRS ~> AfterEnsureNewVRS
                    // Because maxSurge is not supported, this transition can be completed without scaling new VRS
                    assert forall |msg: Message| spec.entails(#[trigger] create_vrs_resp_msg(msg).leads_to(after_ensure_vrs((nv_uid, nv_key, n)))) by {
                        lemma_from_receive_ok_resp_after_create_new_vrs_to_after_ensure_new_vrs(vd, spec, cluster, controller_id, msg, j, n);
                    }
                    leads_to_exists_intro(spec, |msg| create_vrs_resp_msg(msg), after_ensure_vrs((nv_uid, nv_key, n)));
                    leads_to_trans_n!(
                        spec,
                        create_vrs_req(j),
                        create_vrs_resp,
                        after_ensure_vrs((nv_uid, nv_key, n))
                    );
                    // after_ensure_vrs((nv_uid, nv_key, n)) |= \E |i| after_ensure_vrs(i)
                    assert(after_ensure_vrs((nv_uid, nv_key, n)).entails(tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i)))) by {
                        assert forall |ex: Execution<ClusterState>| #[trigger] after_ensure_vrs((nv_uid, nv_key, n)).satisfied_by(ex) implies
                            tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i)).satisfied_by(ex) by {
                            assert((|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i))((nv_uid, nv_key, n)).satisfied_by(ex));
                        }
                    }
                    entails_implies_leads_to(spec, after_ensure_vrs((nv_uid, nv_key, n)), tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i)));
                    // create_vrs_req(j) ~> \E |n| after_ensure_vrs(n)
                    leads_to_trans_n!(
                        spec,
                        create_vrs_req(j),
                        after_ensure_vrs((nv_uid, nv_key, n)),
                        tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i))
                    );
                }
                leads_to_exists_intro(spec, |j: (Uid, ObjectRef)| create_vrs_req(j), tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i)));
                leads_to_trans_n!(
                    spec,
                    after_list_with_etcd_state(msg, None, n),
                    create_vrs_req_nv,
                    tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i))
                );
            } else {
                let (nv_uid, nv_key, replicas) = ((nv_uid_key_replicas->0).0, (nv_uid_key_replicas->0).1, (nv_uid_key_replicas->0).2);
                if replicas != vd.spec.replicas.unwrap_or(int1!()) {
                    let scale_new_vrs_req = lift_state(and!(
                        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
                        pending_get_then_update_new_vrs_req_in_flight(vd, controller_id),
                        etcd_state_is(vd, controller_id, nv_uid_key_replicas, n),
                        local_state_is(vd, controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n)
                    ));
                    // AfterListVRS ~> AfterScaleNewVRS
                    assert(spec.entails(after_list_with_etcd_state(msg, nv_uid_key_replicas, n).leads_to(scale_new_vrs_req))) by {
                        lemma_from_after_receive_list_vrs_resp_to_pending_scale_new_vrs_req_in_flight(vd, spec, cluster, controller_id, msg, nv_uid_key_replicas->0, n);
                    }
                    let scale_new_vrs_req_msg = |msg: Message| lift_state(and!(
                        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
                        req_msg_is_pending_get_then_update_new_vrs_req_in_flight(vd, controller_id, msg),
                        etcd_state_is(vd, controller_id, nv_uid_key_replicas, n),
                        local_state_is(vd, controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n)
                    ));
                    assert(scale_new_vrs_req == tla_exists(|msg| scale_new_vrs_req_msg(msg))) by {
                        assert forall |ex: Execution<ClusterState>| #[trigger] scale_new_vrs_req.satisfied_by(ex) implies
                            tla_exists(|msg| scale_new_vrs_req_msg(msg)).satisfied_by(ex) by {
                            let s = ex.head();
                            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                            assert((|msg| scale_new_vrs_req_msg(msg))(req_msg).satisfied_by(ex));
                        }
                        temp_pred_equality(scale_new_vrs_req, tla_exists(|msg| scale_new_vrs_req_msg(msg)));
                    }
                    let scale_new_vrs_resp = lift_state(and!(
                        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
                        exists_resp_msg_is_ok_get_then_update_resp(vd, controller_id),
                        etcd_state_is(vd, controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n),
                        local_state_is(vd, controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n)
                    ));
                    assert forall |msg: Message| spec.entails(#[trigger] scale_new_vrs_req_msg(msg).leads_to(scale_new_vrs_resp)) by {
                        lemma_from_after_send_get_then_update_req_to_receive_ok_resp_of_new_replicas(vd, spec, cluster, controller_id, msg, nv_uid_key_replicas->0, n);
                    }
                    leads_to_exists_intro(spec, |msg| scale_new_vrs_req_msg(msg), scale_new_vrs_resp);
                    let scale_new_vrs_resp_msg = |msg: Message| lift_state(and!(
                        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
                        resp_msg_is_ok_get_then_update_resp(vd, controller_id, msg),
                        etcd_state_is(vd, controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n),
                        local_state_is(vd, controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n)
                    ));
                    assert(scale_new_vrs_resp == tla_exists(|msg| scale_new_vrs_resp_msg(msg))) by {
                        assert forall |ex: Execution<ClusterState>| #[trigger] scale_new_vrs_resp.satisfied_by(ex) implies
                            tla_exists(|msg| scale_new_vrs_resp_msg(msg)).satisfied_by(ex) by {
                            let s = ex.head();
                            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                            let resp_msg = choose |resp_msg| {
                                &&& #[trigger] s.in_flight().contains(resp_msg)
                                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                                &&& resp_msg.content.is_get_then_update_response()
                                &&& resp_msg.content.get_get_then_update_response().res is Ok
                            };
                            assert((|msg| scale_new_vrs_resp_msg(msg))(resp_msg).satisfied_by(ex));
                        }
                        temp_pred_equality(scale_new_vrs_resp, tla_exists(|msg| scale_new_vrs_resp_msg(msg)));
                    }
                    // AfterScaleNewVRS ~> AfterEnsureNewVRS
                    assert forall |msg: Message| spec.entails(#[trigger] scale_new_vrs_resp_msg(msg).leads_to(after_ensure_vrs((nv_uid, nv_key, n)))) by {
                        lemma_from_receive_ok_resp_after_scale_new_vrs_to_after_ensure_new_vrs(vd, spec, cluster, controller_id, msg, (nv_uid, nv_key), n);
                    }
                    leads_to_exists_intro(spec, |msg| scale_new_vrs_resp_msg(msg), after_ensure_vrs((nv_uid, nv_key, n)));
                    leads_to_trans_n!(
                        spec,
                        after_list_with_etcd_state(msg, nv_uid_key_replicas, n),
                        scale_new_vrs_req,
                        scale_new_vrs_resp,
                        after_ensure_vrs((nv_uid, nv_key, n))
                    );
                } else {
                    assert(spec.entails(after_list_with_etcd_state(msg, nv_uid_key_replicas, n).leads_to(after_ensure_vrs((nv_uid, nv_key, n))))) by {
                        temp_pred_equality(after_ensure_vrs((nv_uid, nv_key, n)), lift_state(and!(
                            at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
                            no_pending_req_in_cluster(vd, controller_id),
                            etcd_state_is(vd, controller_id, nv_uid_key_replicas, n),
                            local_state_is(vd, controller_id, nv_uid_key_replicas, n)
                        )));
                        lemma_from_after_receive_list_vrs_resp_to_after_ensure_new_vrs(vd, spec, cluster, controller_id, msg, nv_uid_key_replicas, n);
                    }
                }
                // after_ensure_vrs((nv_uid, nv_key, n)) ~> \E |i| after_ensure_vrs(i)
                assert(after_ensure_vrs((nv_uid, nv_key, n)).entails(tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i)))) by {
                    assert forall |ex: Execution<ClusterState>| #[trigger] after_ensure_vrs((nv_uid, nv_key, n)).satisfied_by(ex) implies
                        tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i)).satisfied_by(ex) by {
                        assert((|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i))((nv_uid, nv_key, n)).satisfied_by(ex));
                    }
                }
                entails_implies_leads_to(spec, after_ensure_vrs((nv_uid, nv_key, n)), tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i)));
                // after_list_with_etcd_state(msg, replicas, n) ~> \E |i| after_ensure_vrs(i)
                leads_to_trans_n!(
                    spec,
                    after_list_with_etcd_state(msg, nv_uid_key_replicas, n),
                    after_ensure_vrs((nv_uid, nv_key, n)),
                    tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i))
                );
            }
        }
        leads_to_exists_intro(spec, |i: (Option<(Uid, ObjectRef, int)>, nat)| after_list_with_etcd_state(msg, i.0, i.1), tla_exists(|i| after_ensure_vrs(i)));
    }
    // \A |msg| (list_resp_msg(msg) ~> \E |n: nat| after_ensure_vrs((nv_uid, nv_key, n)))
    leads_to_exists_intro(spec, |msg| list_resp_msg(msg), tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i)));
    // Init ~> AfterEnsureNewVRS(n)
    leads_to_trans_n!(
        spec,
        init,
        list_req,
        list_resp,
        tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i))
    );
    let done = lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Done]),
        current_state_matches(vd)
    ));
    // AfterEnsureNewVRS ~> Done
    assert forall |i: (Uid, ObjectRef, nat)| true implies spec.entails(#[trigger] after_ensure_vrs(i).leads_to(done)) by {
        let (nv_uid_key, n) = ((i.0, i.1), i.2);
        let nv_uid_key_replicas = Some((i.0, i.1, vd.spec.replicas.unwrap_or(int1!())));
        if n == 0 {
            // direct transition
            lemma_from_old_vrs_len_zero_after_ensure_new_vrs_to_current_state_matches(vd, spec, cluster, controller_id, nv_uid_key, n);
        } else {
            // send scale down req
            let scale_down_req = lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                pending_get_then_update_old_vrs_req_in_flight(vd, controller_id, nv_uid_key.0),
                etcd_state_is(vd, controller_id, nv_uid_key_replicas, n),
                local_state_is(vd, controller_id, nv_uid_key_replicas, n - nat1!())
            ));
            assert(spec.entails(after_ensure_vrs(i).leads_to(scale_down_req))) by {
                temp_pred_equality(scale_down_req, lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                    pending_get_then_update_old_vrs_req_in_flight(vd, controller_id, nv_uid_key.0),
                    etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
                    local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!())
                )));
                lemma_from_after_ensure_new_vrs_with_old_vrs_of_n_to_pending_scale_down_req_in_flight(vd, spec, cluster, controller_id, nv_uid_key, n);
            }
            let scale_down_req_msg = |msg: Message| lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                req_msg_is_pending_get_then_update_old_vrs_req_in_flight(vd, controller_id, msg, nv_uid_key.0),
                etcd_state_is(vd, controller_id, nv_uid_key_replicas, n),
                local_state_is(vd, controller_id, nv_uid_key_replicas, n - nat1!())
            ));
            assert(scale_down_req == tla_exists(|msg| scale_down_req_msg(msg))) by {
                assert forall |ex: Execution<ClusterState>| #[trigger] scale_down_req.satisfied_by(ex) implies
                    tla_exists(|msg| scale_down_req_msg(msg)).satisfied_by(ex) by {
                    let s = ex.head();
                    let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                    assert((|msg| scale_down_req_msg(msg))(req_msg).satisfied_by(ex));
                }
                temp_pred_equality(scale_down_req, tla_exists(|msg| scale_down_req_msg(msg)));
            }
            // from req to resp
            let scale_down_resp = |n: nat| lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                exists_resp_msg_is_ok_get_then_update_resp(vd, controller_id),
                etcd_state_is(vd, controller_id, nv_uid_key_replicas, n),
                local_state_is(vd, controller_id, nv_uid_key_replicas, n)
            ));
            // from n old vrs to scale down to n - 1 old vrs
            assert forall |msg: Message| spec.entails(#[trigger] scale_down_req_msg(msg).leads_to(scale_down_resp((n - nat1!()) as nat))) by {
                temp_pred_equality(scale_down_req_msg(msg), lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                    req_msg_is_pending_get_then_update_old_vrs_req_in_flight(vd, controller_id, msg, nv_uid_key.0),
                    etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
                    local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!())
                )));
                temp_pred_equality(scale_down_resp((n - nat1!()) as nat), lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                    exists_resp_msg_is_ok_get_then_update_resp(vd, controller_id),
                    etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
                    local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!())
                )));
                lemma_from_after_send_get_then_update_req_to_receive_get_then_update_resp_on_old_vrs_of_n(vd, spec, cluster, controller_id, msg, nv_uid_key, n);
            }
            leads_to_exists_intro(spec, |msg| scale_down_req_msg(msg), scale_down_resp((n - nat1!()) as nat));
            assert forall |n: nat| #![trigger scale_down_resp(n)] n > 0 implies spec.entails(scale_down_resp(n).leads_to(scale_down_resp((n - nat1!()) as nat))) by {
                temp_pred_equality(scale_down_resp(n), lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                    exists_resp_msg_is_ok_get_then_update_resp(vd, controller_id),
                    etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
                    local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
                )));
                temp_pred_equality(scale_down_resp((n - nat1!()) as nat), lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                    exists_resp_msg_is_ok_get_then_update_resp(vd, controller_id),
                    etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
                    local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!())
                )));
                lemma_from_n_to_n_minus_one_on_old_vrs_len(vd, spec, cluster, controller_id, nv_uid_key, n);
            }
            // n ~> n-1 ~..> 0
            assert(spec.entails(scale_down_resp((n - nat1!()) as nat).leads_to(scale_down_resp(nat0!())))) by {
                leads_to_rank_step_one(spec, scale_down_resp);
            }
            // 0 ~> Done
            let scale_down_resp_msg_zero = |msg: Message| lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                resp_msg_is_ok_get_then_update_resp(vd, controller_id, msg),
                etcd_state_is(vd, controller_id, nv_uid_key_replicas, nat0!()),
                local_state_is(vd, controller_id, nv_uid_key_replicas, nat0!())
            ));
            assert(scale_down_resp(nat0!()) == tla_exists(|msg| scale_down_resp_msg_zero(msg))) by {
                assert forall |ex: Execution<ClusterState>| #[trigger] scale_down_resp(nat0!()).satisfied_by(ex) implies
                    tla_exists(|msg| scale_down_resp_msg_zero(msg)).satisfied_by(ex) by {
                    let s = ex.head();
                    let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] s.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.is_get_then_update_response()
                        &&& resp_msg.content.get_get_then_update_response().res is Ok
                    };
                    assert((|msg| scale_down_resp_msg_zero(msg))(resp_msg).satisfied_by(ex));
                }
                temp_pred_equality(scale_down_resp(nat0!()), tla_exists(|msg| scale_down_resp_msg_zero(msg)));
            }
            assert forall |msg: Message| spec.entails(#[trigger] scale_down_resp_msg_zero(msg).leads_to(done)) by {
                temp_pred_equality(scale_down_resp_msg_zero(msg), lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                    resp_msg_is_ok_get_then_update_resp(vd, controller_id, msg),
                    etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!()),
                    local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!())
                )));
                lemma_from_old_vrs_len_zero_at_scale_down_old_vrs_to_current_state_matches(vd, spec, cluster, controller_id, msg, nv_uid_key);
            }
            leads_to_exists_intro(spec, |msg| scale_down_resp_msg_zero(msg), done);
            leads_to_trans_n!(
                spec,
                after_ensure_vrs(i),
                scale_down_req,
                scale_down_resp((n - nat1!()) as nat),
                scale_down_resp(nat0!()),
                done
            );
        }
    }
    leads_to_exists_intro(spec, |i: (Uid, ObjectRef, nat)| after_ensure_vrs(i), done);
    leads_to_trans_n!(
        spec,
        init,
        tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i)),
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
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
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
                let msg = input->0;
                if msg == req_msg {
                    let resp_msg = lemma_list_vrs_request_returns_ok_with_objs_matching_vd(
                        s, s_prime, vd, cluster, controller_id, msg
                    );
                    // instantiate existential quantifier.
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg_is_ok_list_resp_containing_matched_vrs(vd, controller_id, resp_msg, s_prime)
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
        // instantiate existential quantifier.
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg_is_ok_list_resp_containing_matched_vrs(vd, controller_id, resp_msg, s_prime)
        });
    }
    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

// this lemma specifies how VD controller construct the internal cache from list response
#[verifier(external_body)]
proof fn lemma_from_list_resp_to_next_state(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, resp_msg: Message, nv_uid_key_replicas: Option<(Uid, ObjectRef, int)>, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp_msg), Some(vd.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s),
    resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg)(s),
    etcd_state_is(vd, controller_id, nv_uid_key_replicas, n)(s),
ensures
    local_state_is(vd, controller_id, nv_uid_key_replicas, n)(s_prime),
    etcd_state_is(vd, controller_id, nv_uid_key_replicas, n)(s_prime),
    (nv_uid_key_replicas is Some && (nv_uid_key_replicas->0).2 == vd.spec.replicas.unwrap_or(int1!()) ==> {
        &&& at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS])(s_prime)
        &&& local_state_is(vd, controller_id, nv_uid_key_replicas, n)(s_prime)
        &&& no_pending_req_in_cluster(vd, controller_id)(s_prime)
    }),
    (nv_uid_key_replicas is Some && (nv_uid_key_replicas->0).2 != vd.spec.replicas.unwrap_or(int1!()) ==> {
        &&& at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS])(s_prime)
        &&& local_state_is(vd, controller_id, Some(((nv_uid_key_replicas->0).0, (nv_uid_key_replicas->0).1, vd.spec.replicas.unwrap_or(int1!()))), n)(s_prime)
        &&& pending_get_then_update_new_vrs_req_in_flight(vd, controller_id)(s_prime)
    }),
    (nv_uid_key_replicas is None ==> {
        &&& at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS])(s_prime)
        &&& local_state_is(vd, controller_id, Some(((nv_uid_key_replicas->0).0, (nv_uid_key_replicas->0).1, vd.spec.replicas.unwrap_or(int1!()))), n)(s_prime)
        &&& pending_create_new_vrs_req_in_flight(vd, controller_id)(s_prime)
    }),
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    VReplicaSetView::marshal_preserves_integrity();
    broadcast use group_seq_properties;
    let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
    assert(triggering_cr.metadata == vd.metadata);
    assert(triggering_cr.object_ref() == vd.object_ref());
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    let vrs_list_or_none = objects_to_vrs_list(resp_objs);

    let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(vd, vrs_list_or_none->0.filter(|vrs| valid_owned_vrs(vrs, vd)));
    let vrs_list = vrs_list_or_none->0;
    let valid_owned_vrs_filter = |vrs: VReplicaSetView| valid_owned_vrs(vrs, vd);
    assert(valid_owned_vrs_filter == (|vrs: VReplicaSetView| valid_owned_vrs(vrs, triggering_cr)));
    let filtered_vrs_list = vrs_list.filter(valid_owned_vrs_filter);
    let old_vrs_list_filter_with_new_vrs = |vrs: VReplicaSetView| {
        &&& new_vrs is None || vrs.metadata.uid != new_vrs->0.metadata.uid
        &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
    };
    assert(old_vrs_list == filtered_vrs_list.filter(old_vrs_list_filter_with_new_vrs));

    assert((new_vrs, old_vrs_list) == filter_old_and_new_vrs(triggering_cr, vrs_list_or_none->0.filter(|vrs| valid_owned_vrs(vrs, triggering_cr)))) by {
        assert(valid_owned_vrs_filter == (|vrs: VReplicaSetView| valid_owned_vrs(vrs, triggering_cr)));
        assert(filtered_vrs_list == vrs_list.filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, triggering_cr)));
        // new_vrs_filter is the same
        // assert((|vrs: VReplicaSetView| match_template_without_hash(triggering_cr.spec.template, vrs)) == (|vrs: VReplicaSetView| match_template_without_hash(vd.spec.template, vrs)));
        // old_vrs_list_filter_with_new_vrs does not contain vd, skip
    }

    assert forall |vrs| #[trigger] filtered_vrs_list.contains(vrs) implies vrs_list.contains(vrs) && valid_owned_vrs(vrs, vd) by {
        seq_filter_is_a_subset_of_original_seq(vrs_list, valid_owned_vrs_filter);
    }
    assert forall |vrs: VReplicaSetView| #[trigger] old_vrs_list.contains(vrs) implies vrs_list.contains(vrs) && valid_owned_vrs(vrs, vd) by {
        seq_filter_is_a_subset_of_original_seq(filtered_vrs_list, old_vrs_list_filter_with_new_vrs);
    }
    assert(new_vrs is Some ==> vrs_list.contains(new_vrs->0) && valid_owned_vrs(new_vrs->0, vd)) by {
        let new_vrs_filter = |vrs: VReplicaSetView| match_template_without_hash(vd.spec.template, vrs);
        if filtered_vrs_list.filter(new_vrs_filter).len() == 0 {
            assert(new_vrs is None);
        } else {
            seq_filter_is_a_subset_of_original_seq(filtered_vrs_list, new_vrs_filter);
        }
    };
    let map_key = |vrs: VReplicaSetView| vrs.object_ref();
    assert(old_vrs_list.map_values(map_key).no_duplicates()) by {
        assert(old_vrs_list.map_values(map_key).no_duplicates()) by {
            assert(resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref()) == vrs_list.map_values(map_key)) by {
                assert forall |i| 0 <= i < vrs_list.len() implies vrs_list[i].object_ref() == #[trigger] resp_objs[i].object_ref() by {
                    assert(resp_objs.contains(resp_objs[i]));
                }
            }
            map_values_weakens_no_duplicates(vrs_list, map_key);
            seq_filter_preserves_no_duplicates(vrs_list, valid_owned_vrs_filter);
            seq_filter_preserves_no_duplicates(filtered_vrs_list, old_vrs_list_filter_with_new_vrs);
            assert(old_vrs_list.no_duplicates());
            assert forall |vrs| #[trigger] old_vrs_list.contains(vrs) implies vrs_list.contains(vrs) by {
                seq_filter_contains_implies_seq_contains(filtered_vrs_list, old_vrs_list_filter_with_new_vrs, vrs);
                seq_filter_contains_implies_seq_contains(vrs_list, valid_owned_vrs_filter, vrs);
            }
            assert forall |i, j| 0 <= i < old_vrs_list.len() && 0 <= j < old_vrs_list.len() && i != j && old_vrs_list.no_duplicates() implies
                #[trigger] old_vrs_list[i].object_ref() != #[trigger] old_vrs_list[j].object_ref() by {
                assert(old_vrs_list.contains(old_vrs_list[i])); // trigger of vrs_list.contains
                assert(old_vrs_list.contains(old_vrs_list[j]));
                let m = choose |m| 0 <= m < vrs_list.len() && vrs_list[m] == old_vrs_list[i];
                let n = choose |n| 0 <= n < vrs_list.len() && vrs_list[n] == old_vrs_list[j];
                assert(old_vrs_list[i].object_ref() != old_vrs_list[j].object_ref()) by {
                    if m == n {
                        assert(old_vrs_list[i] == old_vrs_list[j]);
                        assert(false);
                    } else {
                        assert(vrs_list[m].object_ref() != vrs_list[n].object_ref()) by {
                            assert(vrs_list.map_values(map_key)[m] == vrs_list[m].object_ref());
                            assert(vrs_list.map_values(map_key)[n] == vrs_list[n].object_ref());
                            assert(vrs_list.map_values(map_key).no_duplicates());
                        }
                    }
                }
            }
        }
    }
    assert forall |vrs| #[trigger] vrs_list.contains(vrs) implies {
        &&& s_prime.resources().contains_key(vrs.object_ref())
        &&& VReplicaSetView::unmarshal(s_prime.resources()[vrs.object_ref()]) is Ok
        &&& VReplicaSetView::unmarshal(s_prime.resources()[vrs.object_ref()])->Ok_0 == vrs
        &&& vrs.metadata.owner_references is Some
        &&& vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
    } by {
        assert(resp_objs.map_values(|o: DynamicObjectView| VReplicaSetView::unmarshal(o).unwrap()).contains(vrs));
        let i = choose |i| #![trigger resp_objs[i]] 0 <= i < resp_objs.len() && resp_objs.map_values(|o: DynamicObjectView| VReplicaSetView::unmarshal(o).unwrap())[i] == vrs;
        assert(resp_objs.contains(resp_objs[i])); // trigger
    }

    let vds = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    let vds_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    assert(vds_prime.old_vrs_list == old_vrs_list);
    assert(vds_prime.old_vrs_index == old_vrs_list.len());
    assert(old_vrs_list.len() == n);
    // replicate transition in reconciler
    assert(match nv_uid_key_replicas {
        None => {
            &&& new_vrs is None
            &&& vds_prime.reconcile_step == AfterCreateNewVRS
            &&& vds_prime.new_vrs == Some(make_replica_set(vd))
            &&& pending_create_new_vrs_req_in_flight(vd, controller_id)(s_prime)
        },
        Some((uid, key, replicas)) => {
            &&& new_vrs is Some
            &&& new_vrs->0.spec.replicas.unwrap_or(int1!()) == replicas
            &&& replicas == vd.spec.replicas.unwrap_or(int1!()) ==> {
                &&& vds_prime.reconcile_step == AfterEnsureNewVRS
                &&& vds_prime.new_vrs == new_vrs
            }
            &&& replicas != vd.spec.replicas.unwrap_or(int1!()) ==> {
                &&& vds_prime.reconcile_step == AfterScaleNewVRS
                &&& vds_prime.new_vrs == Some(VReplicaSetView {
                    spec: VReplicaSetSpecView {
                        replicas: Some(vd.spec.replicas.unwrap_or(int1!())),
                        ..new_vrs->0.spec
                    },
                    ..new_vrs->0
                })
            }
        }
    });

    // prove local_state_is_valid_and_coherent(s_prime)
    assert(forall |i| #![trigger vds_prime.old_vrs_list[i]] 0 <= i < vds_prime.old_vrs_index ==>
        old_vrs_list.contains(vds_prime.old_vrs_list[i])); // trigger
    assert(0 <= vds_prime.old_vrs_index <= vds_prime.old_vrs_list.len());
    assert(vds_prime.old_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref()).no_duplicates());
    if nv_uid_key_replicas is None {
        make_replica_set_makes_valid_owned_vrs(vd);
        assert(vds_prime.new_vrs == Some(make_replica_set(vd)));
        let new_vrs = vds_prime.new_vrs->0;
        let vd_ref_seq = make_owner_references(vd);
        assert(vd_ref_seq == Seq::empty().push(vd.controller_owner_ref()));
        assert(vd_ref_seq.filter(controller_owner_filter()) == vd_ref_seq) by {
            reveal(Seq::filter);
        }
        assert(new_vrs.metadata.owner_references == Some(vd_ref_seq));
    }
}

#[verifier(rlimit(100))]
#[verifier(external_body)]
pub proof fn lemma_from_after_receive_list_vrs_resp_to_after_ensure_new_vrs(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message, nv_uid_key_replicas: Option<(Uid, ObjectRef, int)>, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id))),
    nv_uid_key_replicas is Some,
    (nv_uid_key_replicas->0).2 == vd.spec.replicas.unwrap_or(int1!()),
ensures
    spec.entails(lift_state(and!(
            // at this stage there's no local cache available
            at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
            resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
            etcd_state_is(vd, controller_id, nv_uid_key_replicas, n)
        ))
        .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
            no_pending_req_in_cluster(vd, controller_id),
            etcd_state_is(vd, controller_id, nv_uid_key_replicas, n),
            local_state_is(vd, controller_id, nv_uid_key_replicas, n)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
        etcd_state_is(vd, controller_id, nv_uid_key_replicas, n)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd, controller_id, nv_uid_key_replicas, n),
        local_state_is(vd, controller_id, nv_uid_key_replicas, n)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(vd, cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition_action(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
    );
    let input = (Some(resp_msg), Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
                    s, s_prime, vd, cluster, controller_id, msg, nv_uid_key_replicas, n
                );
                let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                assert forall |obj| #[trigger] resp_objs.contains(obj) implies {
                    &&& s_prime.resources().contains_key(obj.object_ref())
                    &&& s_prime.resources()[obj.object_ref()] == obj
                } by {
                    lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, obj.object_ref(), msg
                    );
                }
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == Some(resp_msg) && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    VReplicaSetView::marshal_preserves_integrity();
                    lemma_from_list_resp_to_next_state(s, s_prime, vd, cluster, controller_id, resp_msg, nv_uid_key_replicas, n);
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
pub proof fn lemma_from_after_receive_list_vrs_resp_to_send_create_new_vrs_req(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
            resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
            etcd_state_is(vd, controller_id, None, n)
        ))
        .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
            pending_create_new_vrs_req_in_flight(vd, controller_id),
            etcd_state_is(vd, controller_id, None, n),
            exists_nv_local_state_is(vd, controller_id, n)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
        etcd_state_is(vd, controller_id, None, n)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
        pending_create_new_vrs_req_in_flight(vd, controller_id),
        etcd_state_is(vd, controller_id, None, n),
        exists_nv_local_state_is(vd, controller_id, n)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(vd, cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition_action(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
    );
    let input = (Some(resp_msg), Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                // nv_uid_key_replicas and n are not yet available
                lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
                    s, s_prime, vd, cluster, controller_id, msg, None, 0
                );
                let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                assert forall |obj| #[trigger] resp_objs.contains(obj) implies {
                    &&& s_prime.resources().contains_key(obj.object_ref())
                    &&& s_prime.resources()[obj.object_ref()] == obj
                } by {
                    lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, obj.object_ref(), msg
                    );
                }
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == Some(resp_msg) && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    VReplicaSetView::marshal_preserves_integrity();
                    lemma_from_list_resp_to_next_state(s, s_prime, vd, cluster, controller_id, resp_msg, None, n);
                }
            },
            _ => {}
        }
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

#[verifier(rlimit(100))]
#[verifier(external_body)]
pub proof fn lemma_from_after_send_create_new_vrs_req_to_receive_ok_resp(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, req_msg: Message, nv_uid_key: (Uid, ObjectRef), n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
            req_msg_is_pending_create_new_vrs_req_in_flight(vd, controller_id, req_msg),
            etcd_state_is(vd, controller_id, None, n),
            local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
            exists_resp_msg_is_ok_create_new_vrs_resp(vd, controller_id),
            etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
        req_msg_is_pending_create_new_vrs_req_in_flight(vd, controller_id, req_msg),
        etcd_state_is(vd, controller_id, None, n),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
        exists_resp_msg_is_ok_create_new_vrs_resp(vd, controller_id),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(vd, cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition_action(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
    );
    let input = Some(req_msg);
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                let msg = input->0;
                if msg == req_msg {
                    let resp_msg = lemma_create_new_vrs_request_returns_ok_after_ensure_new_vrs(
                        s, s_prime, vd, cluster, controller_id, msg, nv_uid_key, n
                    );
                    VReplicaSetView::marshal_preserves_integrity();
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                    });
                } else {
                    let msg = input->0;
                    lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
                        s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n
                    );
                }
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let msg = input->0;
        let resp_msg = lemma_create_new_vrs_request_returns_ok_after_ensure_new_vrs(
            s, s_prime, vd, cluster, controller_id, msg, nv_uid_key, n
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

#[verifier(rlimit(100))]
#[verifier(external_body)]
pub proof fn lemma_from_receive_ok_resp_after_create_new_vrs_to_after_ensure_new_vrs(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message, nv_uid_key: (Uid, ObjectRef), n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
            resp_msg_is_ok_create_new_vrs_resp(vd, controller_id, resp_msg),
            etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
        ))
        .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
            no_pending_req_in_cluster(vd, controller_id),
            etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
        resp_msg_is_ok_create_new_vrs_resp(vd, controller_id, resp_msg),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(vd, cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition_action(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
    );
    let input = (Some(resp_msg), Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
                    s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n
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

#[verifier(rlimit(100))]
#[verifier(external_body)]
pub proof fn lemma_from_after_receive_list_vrs_resp_to_pending_scale_new_vrs_req_in_flight(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message, nv_uid_key_replicas: (Uid, ObjectRef, int), n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id))),
    nv_uid_key_replicas.2 != vd.spec.replicas.unwrap_or(int1!()),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
            resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
            etcd_state_is(vd, controller_id, Some(nv_uid_key_replicas), n)
        ))
        .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
            pending_get_then_update_new_vrs_req_in_flight(vd, controller_id),
            etcd_state_is(vd, controller_id, Some(nv_uid_key_replicas), n),
            local_state_is(vd, controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
        etcd_state_is(vd, controller_id, Some(nv_uid_key_replicas), n)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        pending_get_then_update_new_vrs_req_in_flight(vd, controller_id),
        etcd_state_is(vd, controller_id, Some(nv_uid_key_replicas), n),
        local_state_is(vd, controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(vd, cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition_action(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
    );
    let input = (Some(resp_msg), Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                // nv_uid_key_replicas and n are available
                lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
                    s, s_prime, vd, cluster, controller_id, msg, None, 0
                );
                lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                    s, s_prime, vd, cluster, controller_id, msg, Some(nv_uid_key_replicas), n
                );
                let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                assert forall |obj| #[trigger] resp_objs.contains(obj) implies {
                    &&& s_prime.resources().contains_key(obj.object_ref())
                    &&& s_prime.resources()[obj.object_ref()] == obj
                    &&& VReplicaSetView::unmarshal(obj) is Ok
                    &&& obj.metadata.namespace == vd.metadata.namespace
                } by {
                    lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, obj.object_ref(), msg
                    );
                }
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == Some(resp_msg) && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    VReplicaSetView::marshal_preserves_integrity();
                    lemma_from_list_resp_to_next_state(s, s_prime, vd, cluster, controller_id, resp_msg, Some(nv_uid_key_replicas), n);
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

#[verifier(spinoff_prover)]
#[verifier(rlimit(100))]
#[verifier(external_body)]
pub proof fn lemma_from_after_send_get_then_update_req_to_receive_ok_resp_of_new_replicas(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, req_msg: Message, nv_uid_key_replicas: (Uid, ObjectRef, int), n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id))),
    nv_uid_key_replicas.2 != vd.spec.replicas.unwrap_or(int1!()),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
            req_msg_is_pending_get_then_update_new_vrs_req_in_flight(vd, controller_id, req_msg),
            etcd_state_is(vd, controller_id, Some(nv_uid_key_replicas), n),
            local_state_is(vd, controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
            exists_resp_msg_is_ok_get_then_update_resp(vd, controller_id),
            etcd_state_is(vd, controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd, controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        req_msg_is_pending_get_then_update_new_vrs_req_in_flight(vd, controller_id, req_msg),
        etcd_state_is(vd, controller_id, Some(nv_uid_key_replicas), n),
        local_state_is(vd, controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        exists_resp_msg_is_ok_get_then_update_resp(vd, controller_id),
        etcd_state_is(vd, controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd, controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(vd, cluster, controller_id)(s)
    };
    let input = Some(req_msg);
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition_action(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
    );
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                if msg == req_msg {
                    let resp_msg = lemma_get_then_update_request_returns_ok_after_scale_new_vrs(
                        s, s_prime, vd, cluster, controller_id, msg, nv_uid_key_replicas, n
                    );
                    VReplicaSetView::marshal_preserves_integrity();
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                    });
                } else {
                    let msg = input->0;
                    lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
                        s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n
                    );
                    lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                        s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n
                    );
                    // trigger
                    assert(s.in_flight().contains(msg));
                    assert(msg.src != HostId::Controller(controller_id, vd.object_ref())) by {
                        if msg.src == HostId::Controller(controller_id, vd.object_ref()) {
                            assert(Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), msg));
                            assert(msg == req_msg);
                            assert(false);
                        }
                    }
                    // it's possible to lift the predicate saying the object we care about is not touched during the transition caused by other msg
                    // as a direct result of the boundary predicates and rely conditions
                    // it can be used in both coherent(s) -> coherent(s_prime) and pending_req_msg_is_X(s) -> pending_req_msg_is_X(s_prime)

                    // etcd object is not touched by other msg
                    let key = req_msg.content.get_APIRequest_0().get_GetThenUpdateRequest_0().key();
                    assert(s.resources().contains_key(key));
                    let etcd_obj = s.resources()[key];
                    assert(VReplicaSetView::unmarshal(etcd_obj) is Ok);
                    VReplicaSetView::marshal_preserves_integrity();
                    assert(VReplicaSetView::unmarshal(etcd_obj).unwrap().metadata == etcd_obj.metadata);
                    // rule out cases when etcd_obj get deleted with rely_delete and handle_delete_eq checks
                    assert(etcd_obj.metadata.owner_references->0.contains(vd.controller_owner_ref()));
                    lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, key, msg
                    );
                    assert(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg
                        == s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg);
                    assert(Cluster::pending_req_msg_is(controller_id, s_prime, vd.object_ref(), req_msg));
                    assert(s_prime.in_flight().contains(req_msg));
                }
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let msg = input->0;
        let resp_msg = lemma_get_then_update_request_returns_ok_after_scale_new_vrs(
            s, s_prime, vd, cluster, controller_id, msg, nv_uid_key_replicas, n
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
#[verifier(rlimit(100))]
pub proof fn lemma_from_receive_ok_resp_after_scale_new_vrs_to_after_ensure_new_vrs(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message, nv_uid_key: (Uid, ObjectRef), n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
            resp_msg_is_ok_get_then_update_resp(vd, controller_id, resp_msg),
            etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
        ))
        .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
            no_pending_req_in_cluster(vd, controller_id),
            etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        resp_msg_is_ok_get_then_update_resp(vd, controller_id, resp_msg),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(vd, cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition_action(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
    );
    let input = (Some(resp_msg), Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
                    s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n
                );
                lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                    s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n
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
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, nv_uid_key: (Uid, ObjectRef), n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    n > 0
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
            no_pending_req_in_cluster(vd, controller_id),
            etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
            pending_get_then_update_old_vrs_req_in_flight(vd, controller_id, nv_uid_key.0),
            etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!())
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        pending_get_then_update_old_vrs_req_in_flight(vd, controller_id, nv_uid_key.0),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!())
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(vd, cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition_action(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
    );
    let input = (None::<Message>, Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
                    s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n
                );
                lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                    s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n
                );
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == None::<Message> && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    VReplicaSetView::marshal_preserves_integrity();
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

#[verifier(rlimit(100))]
#[verifier(external_body)]
pub proof fn lemma_from_after_scale_down_old_vrs_with_old_vrs_of_n_to_pending_scale_down_req_in_flight(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message, nv_uid_key: (Uid, ObjectRef), n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    n > 0
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
            resp_msg_is_ok_get_then_update_resp(vd, controller_id, resp_msg),
            etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
            pending_get_then_update_old_vrs_req_in_flight(vd, controller_id, nv_uid_key.0),
            etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!())
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        resp_msg_is_ok_get_then_update_resp(vd, controller_id, resp_msg),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        pending_get_then_update_old_vrs_req_in_flight(vd, controller_id, nv_uid_key.0),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!())
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(vd, cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition_action(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
    );
    let input = (Some(resp_msg), Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
                    s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n
                );
                lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                    s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n
                );
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == Some(resp_msg) && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    VReplicaSetView::marshal_preserves_integrity();
                }
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime)  by {
        VDeploymentReconcileState::marshal_preserves_integrity();
        VReplicaSetView::marshal_preserves_integrity();
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

// TODO: make this proof more stable and faster
#[verifier(spinoff_prover)]
#[verifier(rlimit(100))]
pub proof fn lemma_from_after_send_get_then_update_req_to_receive_get_then_update_resp_on_old_vrs_of_n(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, req_msg: Message, nv_uid_key: (Uid, ObjectRef), n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id))),
    n > 0,
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
            req_msg_is_pending_get_then_update_old_vrs_req_in_flight(vd, controller_id, req_msg, nv_uid_key.0),
            etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!())
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
            exists_resp_msg_is_ok_get_then_update_resp(vd, controller_id),
            etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
            local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!())
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        req_msg_is_pending_get_then_update_old_vrs_req_in_flight(vd, controller_id, req_msg, nv_uid_key.0),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!())
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        exists_resp_msg_is_ok_get_then_update_resp(vd, controller_id),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!())
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(vd, cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition_action(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
    );
    let input = Some(req_msg);
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                if input->0 == req_msg {
                    assume(false); // speedup
                    let resp_msg = lemma_get_then_update_request_returns_ok_after_scale_down_old_vrs(s, s_prime, vd, cluster, controller_id, req_msg, nv_uid_key, n);
                    VReplicaSetView::marshal_preserves_integrity();
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                    });
                    VDeploymentReconcileState::marshal_preserves_integrity();
                } else {
                    let msg = input->0;
                    lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
                        s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), (n - 1) as nat
                    );
                    lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                        s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n
                    );
                    // trigger
                    assert(s.in_flight().contains(msg));
                    assert(msg.src != HostId::Controller(controller_id, vd.object_ref())) by {
                        if msg.src == HostId::Controller(controller_id, vd.object_ref()) {
                            assert(Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), msg));
                            assert(msg == req_msg);
                            assert(false);
                        }
                    }
                    // it's possible to lift the predicate saying the object we care about is not touched during the transition caused by other msg
                    // as a direct result of the boundary predicates and rely conditions
                    // it can be used in both coherent(s) -> coherent(s_prime) and pending_req_msg_is_X(s) -> pending_req_msg_is_X(s_prime)

                    // etcd object is not touched by other msg
                    let key = req_msg.content.get_APIRequest_0().get_GetThenUpdateRequest_0().key();
                    assert(s.resources().contains_key(key));
                    let etcd_obj = s.resources()[key];
                    assert(VReplicaSetView::unmarshal(etcd_obj) is Ok);
                    VReplicaSetView::marshal_preserves_integrity();
                    assert(VReplicaSetView::unmarshal(etcd_obj).unwrap().metadata == etcd_obj.metadata);
                    // rule out cases when etcd_obj get deleted with rely_delete and handle_delete_eq checks
                    assert(etcd_obj.metadata.owner_references->0.contains(vd.controller_owner_ref()));
                    lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, key, msg
                    );
                    assert(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg
                        == s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg);
                    assert(Cluster::pending_req_msg_is(controller_id, s_prime, vd.object_ref(), req_msg));
                    assert(s_prime.in_flight().contains(req_msg));
                    assert(at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS])(s_prime));
                    assert(req_msg_is_pending_get_then_update_old_vrs_req_in_flight(vd, controller_id, req_msg, nv_uid_key.0)(s_prime));
                    assert(etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)(s_prime));
                    assert(local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), (n - nat1!()) as nat)(s_prime));
                }
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let msg = input->0;
        let resp_msg = lemma_get_then_update_request_returns_ok_after_scale_down_old_vrs(s, s_prime, vd, cluster, controller_id, msg, nv_uid_key, n);
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
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, nv_uid_key: (Uid, ObjectRef), n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    n > 0
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
            exists_resp_msg_is_ok_get_then_update_resp(vd, controller_id),
            etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
            exists_resp_msg_is_ok_get_then_update_resp(vd, controller_id),
            etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
            local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!())
        )))),
{
    let scale_resp = |n: nat| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        exists_resp_msg_is_ok_get_then_update_resp(vd, controller_id),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
    ));
    let scale_resp_msg = |msg: Message, n: nat| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        resp_msg_is_ok_get_then_update_resp(vd, controller_id, msg),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
    ));
    let scale_req = |n: nat| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        pending_get_then_update_old_vrs_req_in_flight(vd, controller_id, nv_uid_key.0),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!())
    ));
    let scale_req_msg = |msg: Message, n: nat| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        req_msg_is_pending_get_then_update_old_vrs_req_in_flight(vd, controller_id, msg, nv_uid_key.0),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!())
    ));
    assert forall |resp_msg: Message| n > 0 implies #[trigger]
        spec.entails(scale_resp_msg(resp_msg, n).leads_to(scale_req(n))) by {
        lemma_from_after_scale_down_old_vrs_with_old_vrs_of_n_to_pending_scale_down_req_in_flight(
            vd, spec, cluster, controller_id, resp_msg, nv_uid_key, n
        );
    }
    assert forall |req_msg: Message| n > 0 implies #[trigger]
        spec.entails(scale_req_msg(req_msg, n).leads_to(scale_resp((n - 1) as nat))) by {
        lemma_from_after_send_get_then_update_req_to_receive_get_then_update_resp_on_old_vrs_of_n(
            vd, spec, cluster, controller_id, req_msg, nv_uid_key, n
        );
    }
    leads_to_exists_intro(spec, |resp_msg: Message| scale_resp_msg(resp_msg, n), scale_req(n));
    leads_to_exists_intro(spec, |req_msg: Message| scale_req_msg(req_msg, n), scale_resp((n - 1) as nat));
    assert(scale_req(n) == tla_exists(|msg| scale_req_msg(msg, n))) by {
        assert forall |ex| #[trigger] scale_req(n).satisfied_by(ex) implies
            tla_exists(|req_msg: Message| scale_req_msg(req_msg, n)).satisfied_by(ex) by {
            let req_msg = ex.head().ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
            assert((|msg: Message| scale_req_msg(msg, n))(req_msg).satisfied_by(ex));
        }
        temp_pred_equality(scale_req(n), tla_exists(|msg| scale_req_msg(msg, n)));
    }
    assert(scale_resp(n) == tla_exists(|msg| scale_resp_msg(msg, n))) by {
        assert forall |ex| #[trigger] scale_resp(n).satisfied_by(ex) implies
            tla_exists(|resp_msg: Message| scale_resp_msg(resp_msg, n)).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
            let resp_msg = choose |resp_msg| {
                &&& #[trigger] s.in_flight().contains(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& resp_msg.content.is_get_then_update_response()
                &&& resp_msg.content.get_get_then_update_response().res is Ok
            };
            assert((|msg: Message| scale_resp_msg(msg, n))(resp_msg).satisfied_by(ex));
        }
        temp_pred_equality(scale_resp(n), tla_exists(|msg| scale_resp_msg(msg, n)));
    }
    leads_to_trans_n!(
        spec,
        scale_resp(n),
        scale_req(n),
        scale_resp((n - 1) as nat)
    );
}

#[verifier(rlimit(100))]
pub proof fn lemma_from_old_vrs_len_zero_after_ensure_new_vrs_to_current_state_matches(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, nv_uid_key: (Uid, ObjectRef), n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id))),
    n == 0,
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
            no_pending_req_in_cluster(vd, controller_id),
            etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step!(Done)),
            current_state_matches(vd)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Done]),
        current_state_matches(vd)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(vd, cluster, controller_id)(s)
    };
    always_to_always_later(spec, lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)));
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition_action(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
        later(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))
    );
    let input = (None, Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
                    s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n
                );
                lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                    s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n
                );
                // trigger
                assert(s.in_flight().contains(msg));
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == None::<Message> && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    final_state_to_esr(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n, s_prime);
                }
            },
            _ => {}
        }
    }
    // without this proof will fail
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime)  by {
        VDeploymentReconcileState::marshal_preserves_integrity();
        final_state_to_esr(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n, s_prime);
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

pub proof fn lemma_from_old_vrs_len_zero_at_scale_down_old_vrs_to_current_state_matches(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message, nv_uid_key: (Uid, ObjectRef)
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
            resp_msg_is_ok_get_then_update_resp(vd, controller_id, resp_msg),
            etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!()),
            local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!())
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![Done]),
            current_state_matches(vd)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        resp_msg_is_ok_get_then_update_resp(vd, controller_id, resp_msg),
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!()),
        local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!())
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Done]),
        current_state_matches(vd)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(vd, cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition_action(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
    );
    let input = (Some(resp_msg), Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
                    s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!()
                );
                lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                    s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!()
                )
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == Some(resp_msg) && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    final_state_to_esr(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!(), s_prime);
                }
            },
            _ => {}
        }
    }
    // without this the proof will be 1s slower
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime)  by {
        VDeploymentReconcileState::marshal_preserves_integrity();
        final_state_to_esr(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!(), s_prime);
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

// Havoc function for VDeploymentView.
uninterp spec fn make_vd() -> VDeploymentView;

}