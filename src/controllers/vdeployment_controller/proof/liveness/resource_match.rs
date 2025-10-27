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
use vstd::{seq_lib::*, map_lib::*, multiset::*};
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
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![Init]),
            no_pending_req_in_cluster(vd, controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![Done]),
            no_pending_req_in_cluster(vd, controller_id),
            current_state_matches(vd)
        )))),
{
    let inv = lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id));
    // Init ~> send list req
    let init = lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step![Init]), no_pending_req_in_cluster(vd, controller_id)));
    let list_req = lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]), pending_list_req_in_flight(vd.object_ref(), controller_id)));
    assert(spec.entails(init.leads_to(list_req))) by {
        lemma_from_init_step_to_send_list_vrs_req(vd, spec, cluster, controller_id);
    }
    let list_req_msg = |msg| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        req_msg_is_pending_list_req_in_flight(vd.object_ref(), controller_id, msg)
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
        exists_pending_list_resp_in_flight_and_match_req(vd.object_ref(), controller_id)
    ));
    // \A |msg| (list_req_msg(msg) ~> list_resp)
    assert forall |req_msg: Message| #[trigger] spec.entails(list_req_msg(req_msg).leads_to(list_resp)) by {
        lemma_from_after_send_list_vrs_req_to_receive_list_vrs_resp(vd, spec, cluster, controller_id, req_msg);
    };
    // \A |msg| (list_req_msg(msg) ~> list_resp) |= (\E |msg| list_resp_msg(msg)) ~> list_resp
    leads_to_exists_intro(spec, |req_msg| list_req_msg(req_msg), list_resp);
    let list_resp_msg = |msg| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd.object_ref(), controller_id, msg)
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
                &&& resp_msg_is_ok_list_resp_containing_matched_vrs(vd.object_ref(), controller_id, resp_msg, s)
            };
            assert((|msg| list_resp_msg(msg))(resp_msg).satisfied_by(ex));
        }
        temp_pred_equality(list_resp, tla_exists(|msg| list_resp_msg(msg)));
    };
    temp_pred_equality(list_resp, tla_exists(|msg| list_resp_msg(msg)));
    let after_list_with_etcd_state = |msg: Message, nv_uid_key_replicas: Option<(Uid, ObjectRef, int)>, n: nat| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd.object_ref(), controller_id, msg),
        new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(vd.object_ref(), controller_id, msg, nv_uid_key_replicas, n),
        etcd_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n)
    ));
    let after_ensure_vrs = |i: (Uid, ObjectRef, nat)| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd.object_ref(), controller_id, Some((i.0, i.1, vd.spec.replicas.unwrap_or(int1!()))), i.2),
        local_state_is(vd.object_ref(), controller_id, Some((i.0, i.1, vd.spec.replicas.unwrap_or(int1!()))), i.2),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
    ));
    // from list_resp with different etcd state to different transitions to AfterEnsureNewVRS
    // \A |msg| (list_resp_msg(msg) ~> \E |n: nat| after_ensure_vrs((nv_uid, nv_key, n)))
    assert forall |msg: Message| #![trigger list_resp_msg(msg)]
        spec.entails(list_resp_msg(msg).leads_to(tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i)))) by {
        // (\A |msg|) list_resp_msg(msg) == \E |replicas: Options<int>, n: nat| after_ensure_vrs((nv_uid, nv_key, n))
        // here replicas.is_Some == if new vrs exists, replicas->0 == new_vrs.spec.replicas.unwrap_or(int1!())
        // 1 is the default value if not set
        assert(spec.entails(list_resp_msg(msg).leads_to(tla_exists(|i: (Option<(Uid, ObjectRef, int)>, nat)| after_list_with_etcd_state(msg, i.0, i.1))))) by {
            assert forall |ex: Execution<ClusterState>| #[trigger] list_resp_msg(msg).satisfied_by(ex) && inv.satisfied_by(ex) implies
                tla_exists(|i: (Option<(Uid, ObjectRef, int)>, nat)| after_list_with_etcd_state(msg, i.0, i.1)).satisfied_by(ex) by {
                let s = ex.head();
                let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
                let resp_objs = msg.content.get_list_response().res.unwrap();
                let managed_vrs_list = objects_to_vrs_list(resp_objs).unwrap().filter(|vrs| valid_owned_vrs(vrs, triggering_cr));
                let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(triggering_cr, managed_vrs_list);
                let nv_uid_key_replicas = if new_vrs is Some {
                    let vrs = new_vrs->0;
                    Some((vrs.metadata.uid->0, vrs.object_ref(), vrs.spec.replicas.unwrap_or(int1!())))
                } else {
                    None
                };
                assert(new_vrs is Some ==> {
                    &&& new_vrs->0.metadata.uid is Some
                    &&& new_vrs->0.metadata.name is Some
                    &&& new_vrs->0.metadata.namespace is Some
                }) by {
                    if new_vrs is Some {
                        let nonempty_vrs_filter = |vrs: VReplicaSetView| vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0;
                        seq_filter_is_a_subset_of_original_seq(managed_vrs_list, match_template_without_hash(triggering_cr.spec.template));
                        if managed_vrs_list.filter(match_template_without_hash(triggering_cr.spec.template)).filter(nonempty_vrs_filter).len() > 0 {
                            seq_filter_is_a_subset_of_original_seq(managed_vrs_list.filter(match_template_without_hash(triggering_cr.spec.template)), nonempty_vrs_filter);
                        }
                    }
                }
                lemma_filter_old_and_new_vrs_from_resp_objs_implies_etcd_state_is(vd, cluster, controller_id, nv_uid_key_replicas, old_vrs_list.len(), msg, s);
                assert((|i: (Option<(Uid, ObjectRef, int)>, nat)| after_list_with_etcd_state(msg, i.0, i.1))((nv_uid_key_replicas, old_vrs_list.len())).satisfied_by(ex));
            }
            entails_implies_leads_to(spec, list_resp_msg(msg).and(inv), tla_exists(|i: (Option<(Uid, ObjectRef, int)>, nat)| after_list_with_etcd_state(msg, i.0, i.1)));
            leads_to_by_borrowing_inv(spec, list_resp_msg(msg), tla_exists(|i: (Option<(Uid, ObjectRef, int)>, nat)| after_list_with_etcd_state(msg, i.0, i.1)), inv);
        }
        // \A |replicas, n| etcd_state_is(replicas, n) ~> \E |n| after_ensure_vrs((nv_uid, nv_key, n))
        assert forall |i: (Option<(Uid, ObjectRef, int)>, nat)| #![trigger after_list_with_etcd_state(msg, i.0, i.1)]
            spec.entails(after_list_with_etcd_state(msg, i.0, i.1).leads_to(tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i)))) by {
            let (nv_uid_key_replicas, n) = i;
            // new vrs does not exists. Here the existance is encoded as is_Some, and replicas is get_Some_0
            if nv_uid_key_replicas is None {
                // AfterListVRS ~> AfterCreateNewVRS
                let create_vrs_req = lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
                    pending_create_new_vrs_req_in_flight(vd.object_ref(), controller_id),
                    etcd_state_is(vd.object_ref(), controller_id, None, n),
                    local_state_is(vd.object_ref(), controller_id, None, n),
                    local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
                ));
                assert(spec.entails(after_list_with_etcd_state(msg, None, n).leads_to(create_vrs_req))) by {
                    lemma_from_after_receive_list_vrs_resp_to_send_create_new_vrs_req(vd, spec, cluster, controller_id, msg, n);
                }
                let create_vrs_req_msg = |msg: Message| lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
                    req_msg_is_pending_create_new_vrs_req_in_flight(vd.object_ref(), controller_id, msg),
                    etcd_state_is(vd.object_ref(), controller_id, None, n),
                    local_state_is(vd.object_ref(), controller_id, None, n),
                    local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
                ));
                assert(create_vrs_req == tla_exists(|msg| create_vrs_req_msg(msg))) by {
                    assert forall |ex: Execution<ClusterState>| #[trigger] create_vrs_req.satisfied_by(ex) implies
                        tla_exists(|msg| create_vrs_req_msg(msg)).satisfied_by(ex) by {
                        let s = ex.head();
                        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                        assert((|msg| create_vrs_req_msg(msg))(req_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(create_vrs_req, tla_exists(|msg| create_vrs_req_msg(msg)));
                }
                // TEST: is it possible to lift quantifier here
                let create_vrs_resp = lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
                    exists_create_resp_msg_containing_new_vrs_uid_key(vd.object_ref(), controller_id, n),
                    local_state_is(vd.object_ref(), controller_id, None, n),
                    local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
                ));
                assert forall |msg| spec.entails(#[trigger] create_vrs_req_msg(msg).leads_to(create_vrs_resp)) by {
                    lemma_from_after_send_create_new_vrs_req_to_receive_ok_resp(vd, spec, cluster, controller_id, msg, n);
                }
                leads_to_exists_intro(spec, |msg| create_vrs_req_msg(msg), create_vrs_resp);
                let create_vrs_resp_msg_nv = |msg, nv_uid_key| lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
                    resp_msg_is_ok_create_new_vrs_resp(vd.object_ref(), controller_id, msg, nv_uid_key),
                    etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
                    local_state_is(vd.object_ref(), controller_id, None, n),
                    local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
                ));
                assert(spec.entails(create_vrs_resp.leads_to(tla_exists(|j: (Message, (Uid, ObjectRef))| create_vrs_resp_msg_nv(j.0, j.1))))) by {
                    assert forall |ex: Execution<ClusterState>| #[trigger] create_vrs_resp.satisfied_by(ex) && inv.satisfied_by(ex) implies
                        tla_exists(|j: (Message, (Uid, ObjectRef))| create_vrs_resp_msg_nv(j.0, j.1)).satisfied_by(ex) by {
                        let s = ex.head();
                        assert(cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s));
                        let (resp_msg, nv_uid_key) = lemma_instantiate_exists_create_resp_msg_containing_new_vrs_uid_key(vd, cluster, controller_id, n, s);
                        assert((|j: (Message, (Uid, ObjectRef))| create_vrs_resp_msg_nv(j.0, j.1))((resp_msg, nv_uid_key)).satisfied_by(ex));
                    }
                    entails_implies_leads_to(spec, create_vrs_resp.and(inv), tla_exists(|j: (Message, (Uid, ObjectRef))| create_vrs_resp_msg_nv(j.0, j.1)));
                    leads_to_by_borrowing_inv(spec, create_vrs_resp, tla_exists(|j: (Message, (Uid, ObjectRef))| create_vrs_resp_msg_nv(j.0, j.1)), inv);
                }
                assert forall |j: (Message, (Uid, ObjectRef))| #![trigger create_vrs_resp_msg_nv(j.0, j.1)]
                    spec.entails(create_vrs_resp_msg_nv(j.0, j.1).leads_to(tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i)))) by {
                    let (nv_uid, nv_key) = j.1;
                    // AfterCreateNewVRS ~> AfterEnsureNewVRS
                    // Because maxSurge is not supported, this transition can be completed without scaling new VRS
                    assert(spec.entails(#[trigger] create_vrs_resp_msg_nv(j.0, j.1).leads_to(after_ensure_vrs((nv_uid, nv_key, n))))) by {
                        lemma_from_receive_ok_resp_after_create_new_vrs_to_after_ensure_new_vrs(vd, spec, cluster, controller_id, j.0, j.1, n);
                    }
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
                        create_vrs_resp_msg_nv(j.0, j.1),
                        after_ensure_vrs((nv_uid, nv_key, n)),
                        tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i))
                    );
                }
                leads_to_exists_intro(spec, |j: (Message, (Uid, ObjectRef))| create_vrs_resp_msg_nv(j.0, j.1), tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i)));
                leads_to_trans_n!(
                    spec,
                    after_list_with_etcd_state(msg, None, n),
                    create_vrs_req,
                    create_vrs_resp,
                    tla_exists(|j: (Message, (Uid, ObjectRef))| create_vrs_resp_msg_nv(j.0, j.1)),
                    tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i))
                );
            } else {
                let (nv_uid, nv_key, replicas) = ((nv_uid_key_replicas->0).0, (nv_uid_key_replicas->0).1, (nv_uid_key_replicas->0).2);
                if replicas != vd.spec.replicas.unwrap_or(int1!()) {
                    let scale_new_vrs_req = lift_state(and!(
                        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
                        pending_scale_new_vrs_req_in_flight(vd.object_ref(), controller_id, (nv_uid, nv_key)),
                        etcd_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n),
                        local_state_is(vd.object_ref(), controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n),
                        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
                    ));
                    // AfterListVRS ~> AfterScaleNewVRS
                    assert(spec.entails(after_list_with_etcd_state(msg, nv_uid_key_replicas, n).leads_to(scale_new_vrs_req))) by {
                        lemma_from_after_receive_list_vrs_resp_to_pending_scale_new_vrs_req_in_flight(vd, spec, cluster, controller_id, msg, nv_uid_key_replicas->0, n);
                    }
                    let scale_new_vrs_req_msg = |msg: Message| lift_state(and!(
                        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
                        req_msg_is_pending_scale_new_vrs_req_in_flight(vd.object_ref(), controller_id, msg, (nv_uid, nv_key)),
                        etcd_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n),
                        local_state_is(vd.object_ref(), controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n),
                        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
                        exists_resp_msg_is_ok_scale_new_vrs_resp_in_flight(vd.object_ref(), controller_id, (nv_uid, nv_key)),
                        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n),
                        local_state_is(vd.object_ref(), controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n),
                        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
                    ));
                    assert forall |msg: Message| spec.entails(#[trigger] scale_new_vrs_req_msg(msg).leads_to(scale_new_vrs_resp)) by {
                        lemma_from_after_send_get_then_update_req_to_receive_ok_resp_of_new_replicas(vd, spec, cluster, controller_id, msg, nv_uid_key_replicas->0, n);
                    }
                    leads_to_exists_intro(spec, |msg| scale_new_vrs_req_msg(msg), scale_new_vrs_resp);
                    let scale_new_vrs_resp_msg = |msg: Message| lift_state(and!(
                        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
                        resp_msg_is_ok_scale_new_vrs_resp_in_flight(vd.object_ref(), controller_id, msg, (nv_uid, nv_key)),
                        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n),
                        local_state_is(vd.object_ref(), controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(int1!()))), n),
                        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
                            etcd_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n),
                            local_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n),
                            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
        leads_to_trans_n!(
            spec,
            list_resp_msg(msg),
            tla_exists(|i: (Option<(Uid, ObjectRef, int)>, nat)| after_list_with_etcd_state(msg, i.0, i.1)),
            tla_exists(|i: (Uid, ObjectRef, nat)| after_ensure_vrs(i))
        );
    }
    // \A |msg| (list_resp_msg(msg) ~> \E |n: nat| after_ensure_vrs((nv_uid, nv_key, n)))
    leads_to_exists_intro(spec, |msg| list_resp_msg(msg), tla_exists(|i| after_ensure_vrs(i)));
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
        no_pending_req_in_cluster(vd, controller_id),
        current_state_matches(vd)
    ));
    // AfterEnsureNewVRS ~> Done
    assert forall |i: (Uid, ObjectRef, nat)| spec.entails(#[trigger] after_ensure_vrs(i).leads_to(done)) by {
        let (nv_uid_key, n) = ((i.0, i.1), i.2);
        let nv_uid_key_replicas = Some((i.0, i.1, vd.spec.replicas.unwrap_or(int1!())));
        if n == 0 {
            // direct transition
            lemma_from_old_vrs_len_zero_after_ensure_new_vrs_to_current_state_matches(vd, spec, cluster, controller_id, nv_uid_key, n);
        } else {
            // send scale down req
            let scale_down_req = lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                pending_scale_old_vrs_req_in_flight(vd.object_ref(), controller_id, nv_uid_key.0),
                etcd_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n),
                local_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n - nat1!()),
                local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
            ));
            assert(spec.entails(after_ensure_vrs(i).leads_to(scale_down_req))) by {
                temp_pred_equality(scale_down_req, lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                    pending_scale_old_vrs_req_in_flight(vd.object_ref(), controller_id, nv_uid_key.0),
                    etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
                    local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
                local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
                )));
                lemma_from_after_ensure_new_vrs_with_old_vrs_of_n_to_pending_scale_down_req_in_flight(vd, spec, cluster, controller_id, nv_uid_key, n);
            }
            let scale_down_req_msg = |msg: Message| lift_state(and!(
                at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                req_msg_is_pending_scale_old_vrs_req_in_flight(vd.object_ref(), controller_id, msg, nv_uid_key.0),
                etcd_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n),
                local_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n - nat1!()),
                local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
                exists_resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd.object_ref(), controller_id, nv_uid_key.0),
                etcd_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n),
                local_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n),
                local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
            ));
            // from n old vrs to scale down to n - 1 old vrs
            assert forall |msg: Message| spec.entails(#[trigger] scale_down_req_msg(msg).leads_to(scale_down_resp((n - nat1!()) as nat))) by {
                temp_pred_equality(scale_down_req_msg(msg), lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                    req_msg_is_pending_scale_old_vrs_req_in_flight(vd.object_ref(), controller_id, msg, nv_uid_key.0),
                    etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
                    local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
                    local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
                )));
                temp_pred_equality(scale_down_resp((n - nat1!()) as nat), lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                    exists_resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd.object_ref(), controller_id, nv_uid_key.0),
                    etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
                    local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
                    local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
                )));
                lemma_from_after_send_get_then_update_req_to_receive_get_then_update_resp_on_old_vrs_of_n(vd, spec, cluster, controller_id, msg, nv_uid_key, n);
            }
            leads_to_exists_intro(spec, |msg| scale_down_req_msg(msg), scale_down_resp((n - nat1!()) as nat));
            assert forall |n: nat| #![trigger scale_down_resp(n)] n > 0 implies spec.entails(scale_down_resp(n).leads_to(scale_down_resp((n - nat1!()) as nat))) by {
                temp_pred_equality(scale_down_resp(n), lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                    exists_resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd.object_ref(), controller_id, nv_uid_key.0),
                    etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
                    local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
                    local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
                )));
                temp_pred_equality(scale_down_resp((n - nat1!()) as nat), lift_state(and!(
                    at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
                    exists_resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd.object_ref(), controller_id, nv_uid_key.0),
                    etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
                    local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
                    local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
                resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd.object_ref(), controller_id, msg, nv_uid_key.0),
                etcd_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, nat0!()),
                local_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, nat0!()),
                local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
                    resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd.object_ref(), controller_id, msg, nv_uid_key.0),
                    etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!()),
                    local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!()),
                    local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]), pending_list_req_in_flight(vd.object_ref(), controller_id))))),
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Init]),
        no_pending_req_in_cluster(vd, controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        pending_list_req_in_flight(vd.object_ref(), controller_id)
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
    spec.entails(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]), req_msg_is_pending_list_req_in_flight(vd.object_ref(), controller_id, req_msg)))
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]), exists_pending_list_resp_in_flight_and_match_req(vd.object_ref(), controller_id))))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        req_msg_is_pending_list_req_in_flight(vd.object_ref(), controller_id, req_msg)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        exists_pending_list_resp_in_flight_and_match_req(vd.object_ref(), controller_id)
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
                        &&& resp_msg_is_ok_list_resp_containing_matched_vrs(vd.object_ref(), controller_id, resp_msg, s_prime)
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
            &&& resp_msg_is_ok_list_resp_containing_matched_vrs(vd.object_ref(), controller_id, resp_msg, s_prime)
        });
    }
    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

// this lemma specifies how VD controller construct the internal cache from list response
proof fn lemma_from_list_resp_to_next_state(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, resp_msg: Message, nv_uid_key_replicas: Option<(Uid, ObjectRef, int)>, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp_msg), Some(vd.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s),
    resp_msg_is_pending_list_resp_in_flight_and_match_req(vd.object_ref(), controller_id, resp_msg)(s),
    new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(vd.object_ref(), controller_id, resp_msg, nv_uid_key_replicas, n)(s),
    etcd_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n)(s),
ensures
    local_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n)(s_prime),
    local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)(s_prime),
    etcd_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n)(s_prime),
    (nv_uid_key_replicas is Some && (nv_uid_key_replicas->0).2 == vd.spec.replicas.unwrap_or(int1!()) ==> {
        &&& at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS])(s_prime)
        &&& local_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n)(s_prime)
        &&& local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)(s_prime)
        &&& no_pending_req_in_cluster(vd, controller_id)(s_prime)
    }),
    (nv_uid_key_replicas is Some && (nv_uid_key_replicas->0).2 != vd.spec.replicas.unwrap_or(int1!()) ==> {
        &&& at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS])(s_prime)
        &&& local_state_is(vd.object_ref(), controller_id, Some(((nv_uid_key_replicas->0).0, (nv_uid_key_replicas->0).1, vd.spec.replicas.unwrap_or(int1!()))), n)(s_prime)
        &&& local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)(s_prime)
        &&& pending_scale_new_vrs_req_in_flight(vd.object_ref(), controller_id, ((nv_uid_key_replicas->0).0, (nv_uid_key_replicas->0).1))(s_prime)
    }),
    (nv_uid_key_replicas is None ==> {
        &&& at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS])(s_prime)
        &&& local_state_is(vd.object_ref(), controller_id, None, n)(s_prime)
        &&& local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)(s_prime)
        &&& pending_create_new_vrs_req_in_flight(vd.object_ref(), controller_id)(s_prime)
    }),
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    VReplicaSetView::marshal_preserves_integrity();
    broadcast use group_seq_properties;
    let vd = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    assert(objects_to_vrs_list(resp_objs) is Some);
    let vrs_list = objects_to_vrs_list(resp_objs)->0;
    let managed_vrs_list = objects_to_vrs_list(resp_objs)->0.filter(|vrs| valid_owned_vrs(vrs, vd));
    let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(vd, managed_vrs_list);
    let new_vrs_uid = if nv_uid_key_replicas is Some { Some((nv_uid_key_replicas->0).0) } else { None };
    let valid_owned_vrs_filter = |vrs: VReplicaSetView| valid_owned_vrs(vrs, vd);
    let managed_vrs_list = vrs_list.filter(valid_owned_vrs_filter);
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
        &&& new_vrs is None || vrs.metadata.uid != new_vrs->0.metadata.uid
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
            if new_vrs is None {
                assert(new_vrs_uid is None);
            } else {
                assert(vrs.metadata.uid is Some);
                assert(new_vrs_uid is Some);
                assert(new_vrs->0.metadata.uid == new_vrs_uid);
            }
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
    assert(new_vrs is Some ==> managed_vrs_list.contains(new_vrs->0) && vrs_list.contains(new_vrs->0) && valid_owned_vrs(new_vrs->0, vd)) by {
        assert(new_vrs is Some ==> managed_vrs_list.contains(new_vrs->0)) by { // trigger
            // unwrap filter_old_and_new_vrs
            let non_zero_replicas_filter = |vrs: VReplicaSetView| vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0;
            if managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).len() > 0 {
                seq_filter_is_a_subset_of_original_seq(managed_vrs_list, match_template_without_hash(vd.spec.template));
                if managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(non_zero_replicas_filter).len() > 0 {
                    assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(non_zero_replicas_filter).contains(new_vrs->0));
                    seq_filter_is_a_subset_of_original_seq(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)), non_zero_replicas_filter);
                }
                assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).contains(new_vrs->0));
            } else {
                assert(new_vrs is None);
            }
        }
    };
    let map_key = |vrs: VReplicaSetView| vrs.object_ref();
    assert(old_vrs_list.map_values(map_key).no_duplicates()) by {
        lemma_no_duplication_in_resp_objs_implies_no_duplication_in_down_stream(vd, resp_objs);
    }
    assert(old_vrs_list.map_values(map_key).to_set()
        == filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(new_vrs_uid, s))) by {
        lemma_old_vrs_filter_on_objs_eq_filter_on_keys(vd, managed_vrs_list, new_vrs_uid, s);
    }
    assert(old_vrs_list.len() == n) by {
        old_vrs_list.map_values(map_key).unique_seq_to_set();
        assert(old_vrs_list.map_values(map_key).len() == old_vrs_list.len());
        assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(new_vrs_uid, s)).len() == n);
    }

    let vds = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    let vds_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    assert(vds_prime.old_vrs_list == old_vrs_list);
    assert(vds_prime.old_vrs_index == old_vrs_list.len());

    // prove local_state_is_coherent_with_etcd_valid_and_coherent(s_prime)
    assert(forall |i| #![trigger vds_prime.old_vrs_list[i]] 0 <= i < vds_prime.old_vrs_index ==>
        old_vrs_list.contains(vds_prime.old_vrs_list[i]) && managed_vrs_list.contains(vds_prime.old_vrs_list[i])); // trigger
}

#[verifier(rlimit(100))]
#[verifier(spinoff_prover)]
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
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    nv_uid_key_replicas is Some,
    (nv_uid_key_replicas->0).2 == vd.spec.replicas.unwrap_or(int1!()),
ensures
    spec.entails(lift_state(and!(
            // at this stage there's no local cache available
            at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
            resp_msg_is_pending_list_resp_in_flight_and_match_req(vd.object_ref(), controller_id, resp_msg),
            new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(vd.object_ref(), controller_id, resp_msg, nv_uid_key_replicas, n),
            etcd_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n)
        ))
        .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
            no_pending_req_in_cluster(vd, controller_id),
            etcd_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n),
            local_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd.object_ref(), controller_id, resp_msg),
        new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(vd.object_ref(), controller_id, resp_msg, nv_uid_key_replicas, n),
        etcd_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n),
        local_state_is(vd.object_ref(), controller_id, nv_uid_key_replicas, n),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
                assert(pre(s_prime)) by {
                    
                    let msg = input->0;
                    lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                        s, s_prime, vd, cluster, controller_id, msg, nv_uid_key_replicas, n
                    );
                    lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key_replicas->0).0)
                    );
                    // prove coherence part in resp_msg_is_ok_list_resp_containing_matched_vrs
                    let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
                    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                    let managed_vrs_list = objects_to_vrs_list(resp_objs)->0.filter(|vrs| valid_owned_vrs(vrs, triggering_cr));
                    assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies {
                        &&& s_prime.resources().contains_key(vrs.object_ref())
                        &&& s_prime.resources()[vrs.object_ref()] == s.resources()[vrs.object_ref()]
                    } by {
                        let obj = s.resources()[vrs.object_ref()];
                        assert(obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![triggering_cr.controller_owner_ref()]) by {
                            let etcd_vrs = VReplicaSetView::unmarshal(obj)->Ok_0;
                            assert(VReplicaSetView::unmarshal(obj) is Ok);
                            VReplicaSetView::marshal_preserves_integrity();
                            assert(vrs_weakly_eq(etcd_vrs, vrs));
                        }
                        lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
                            s, s_prime, vd, cluster, controller_id, msg
                        );
                    }
                    assert(s_prime.in_flight().contains(resp_msg));
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

#[verifier(rlimit(100))]
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
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
            resp_msg_is_pending_list_resp_in_flight_and_match_req(vd.object_ref(), controller_id, resp_msg),
            new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(vd.object_ref(), controller_id, resp_msg, None, n),
            etcd_state_is(vd.object_ref(), controller_id, None, n)
        ))
        .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
            pending_create_new_vrs_req_in_flight(vd.object_ref(), controller_id),
            etcd_state_is(vd.object_ref(), controller_id, None, n),
            local_state_is(vd.object_ref(), controller_id, None, n),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd.object_ref(), controller_id, resp_msg),
        new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(vd.object_ref(), controller_id, resp_msg, None, n),
        etcd_state_is(vd.object_ref(), controller_id, None, n)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
        pending_create_new_vrs_req_in_flight(vd.object_ref(), controller_id),
        etcd_state_is(vd.object_ref(), controller_id, None, n),
        local_state_is(vd.object_ref(), controller_id, None, n),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
                lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                    s, s_prime, vd, cluster, controller_id, msg, None, n
                );
                lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
                    s, s_prime, vd, cluster, controller_id, msg, None
                );
                VDeploymentView::marshal_preserves_integrity();
                let vd = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr)->Ok_0;
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
                    &&& vrs_weakly_eq(etcd_vrs, vrs)
                    &&& etcd_vrs.spec == vrs.spec
                } by {
                    lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, msg
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
pub proof fn lemma_from_after_send_create_new_vrs_req_to_receive_ok_resp(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, req_msg: Message, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
            req_msg_is_pending_create_new_vrs_req_in_flight(vd.object_ref(), controller_id, req_msg),
            etcd_state_is(vd.object_ref(), controller_id, None, n),
            local_state_is(vd.object_ref(), controller_id, None, n),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
            exists_create_resp_msg_containing_new_vrs_uid_key(vd.object_ref(), controller_id, n),
            local_state_is(vd.object_ref(), controller_id, None, n),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
        req_msg_is_pending_create_new_vrs_req_in_flight(vd.object_ref(), controller_id, req_msg),
        etcd_state_is(vd.object_ref(), controller_id, None, n),
        local_state_is(vd.object_ref(), controller_id, None, n),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
        exists_create_resp_msg_containing_new_vrs_uid_key(vd.object_ref(), controller_id, n),
        local_state_is(vd.object_ref(), controller_id, None, n),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
    let input = Some(req_msg);
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                if msg == req_msg {
                    let (resp_msg, nv_uid_key) = lemma_create_new_vrs_request_returns_ok(
                        s, s_prime, vd, cluster, controller_id, msg, n
                    );
                    VReplicaSetView::marshal_preserves_integrity();
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg_is_ok_create_resp_containing_new_vrs(vd.object_ref(), controller_id, resp_msg, nv_uid_key, s_prime)
                        &&& etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)(s_prime)
                    });
                } else {
                    let msg = input->0;
                    lemma_api_request_other_than_pending_req_msg_maintains_local_state_validity_and_coherence(s, s_prime, vd, cluster, controller_id, msg);
                    lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                        s, s_prime, vd, cluster, controller_id, msg, None, n
                    );
                }
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let msg = input->0;
        let (resp_msg, nv_uid_key) = lemma_create_new_vrs_request_returns_ok(
            s, s_prime, vd, cluster, controller_id, msg, n
        );
        VReplicaSetView::marshal_preserves_integrity();
        // instantiate existential quantifier.
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg_is_ok_create_resp_containing_new_vrs(vd.object_ref(), controller_id, resp_msg, nv_uid_key, s_prime)
            &&& etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)(s_prime)
        });
    }
    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

#[verifier(rlimit(100))]
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
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
            resp_msg_is_ok_create_new_vrs_resp(vd.object_ref(), controller_id, resp_msg, nv_uid_key),
            etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd.object_ref(), controller_id, None, n),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        ))
        .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
            no_pending_req_in_cluster(vd, controller_id),
            etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS]),
        resp_msg_is_ok_create_new_vrs_resp(vd.object_ref(), controller_id, resp_msg, nv_uid_key),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd.object_ref(), controller_id, None, n),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
                lemma_api_request_other_than_pending_req_msg_maintains_local_state_validity_and_coherence(s, s_prime, vd, cluster, controller_id, msg);
                lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                    s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n
                );
                lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
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

#[verifier(rlimit(100))]
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
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    nv_uid_key_replicas.2 != vd.spec.replicas.unwrap_or(int1!()),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
            resp_msg_is_pending_list_resp_in_flight_and_match_req(vd.object_ref(), controller_id, resp_msg),
            new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(vd.object_ref(), controller_id, resp_msg, Some(nv_uid_key_replicas), n),
            etcd_state_is(vd.object_ref(), controller_id, Some(nv_uid_key_replicas), n)
        ))
        .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
            pending_scale_new_vrs_req_in_flight(vd.object_ref(), controller_id, (nv_uid_key_replicas.0, nv_uid_key_replicas.1)),
            etcd_state_is(vd.object_ref(), controller_id, Some(nv_uid_key_replicas), n),
            local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd.object_ref(), controller_id, resp_msg),
        new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(vd.object_ref(), controller_id, resp_msg, Some(nv_uid_key_replicas), n),
        etcd_state_is(vd.object_ref(), controller_id, Some(nv_uid_key_replicas), n)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        pending_scale_new_vrs_req_in_flight(vd.object_ref(), controller_id, (nv_uid_key_replicas.0, nv_uid_key_replicas.1)),
        etcd_state_is(vd.object_ref(), controller_id, Some(nv_uid_key_replicas), n),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
                lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                    s, s_prime, vd, cluster, controller_id, msg, Some(nv_uid_key_replicas), n
                );
                lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
                    s, s_prime, vd, cluster, controller_id, msg, Some(nv_uid_key_replicas.0)
                );
                VDeploymentView::marshal_preserves_integrity();
                let vd = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr)->Ok_0;
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
                    &&& vrs_weakly_eq(etcd_vrs, vrs)
                    &&& etcd_vrs.spec == vrs.spec
                } by {
                    lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, msg
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

#[verifier(rlimit(100))]
#[verifier(spinoff_prover)]
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
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    nv_uid_key_replicas.2 != vd.spec.replicas.unwrap_or(int1!()),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
            req_msg_is_pending_scale_new_vrs_req_in_flight(vd.object_ref(), controller_id, req_msg, (nv_uid_key_replicas.0, nv_uid_key_replicas.1)),
            etcd_state_is(vd.object_ref(), controller_id, Some(nv_uid_key_replicas), n),
            local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
            exists_resp_msg_is_ok_scale_new_vrs_resp_in_flight(vd.object_ref(), controller_id, (nv_uid_key_replicas.0, nv_uid_key_replicas.1)),
            etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        req_msg_is_pending_scale_new_vrs_req_in_flight(vd.object_ref(), controller_id, req_msg, (nv_uid_key_replicas.0, nv_uid_key_replicas.1)),
        etcd_state_is(vd.object_ref(), controller_id, Some(nv_uid_key_replicas), n),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        exists_resp_msg_is_ok_scale_new_vrs_resp_in_flight(vd.object_ref(), controller_id, (nv_uid_key_replicas.0, nv_uid_key_replicas.1)),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(cluster, controller_id)(s)
    };
    let input = Some(req_msg);
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
    );
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                if msg == req_msg {
                    // TODO: investigate why this branch is super slow
                    let resp_msg = lemma_scale_new_vrs_req_returns_ok(
                        s, s_prime, vd, cluster, controller_id, msg, nv_uid_key_replicas, n
                    );
                    VReplicaSetView::marshal_preserves_integrity();
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                    });
                } else {
                    let msg = input->0;
                    lemma_api_request_other_than_pending_req_msg_maintains_local_state_validity_and_coherence(s, s_prime, vd, cluster, controller_id, msg);
                    lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                        s, s_prime, vd, cluster, controller_id, msg, Some(nv_uid_key_replicas), n
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
                    lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, msg
                    );
                    assert(s_prime.in_flight().contains(req_msg));
                }
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let msg = input->0;
        let resp_msg = lemma_scale_new_vrs_req_returns_ok(
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
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
            resp_msg_is_ok_scale_new_vrs_resp_in_flight(vd.object_ref(), controller_id, resp_msg, nv_uid_key),
            etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        ))
        .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
            no_pending_req_in_cluster(vd, controller_id),
            etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        resp_msg_is_ok_scale_new_vrs_resp_in_flight(vd.object_ref(), controller_id, resp_msg, nv_uid_key),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
                lemma_api_request_other_than_pending_req_msg_maintains_local_state_validity_and_coherence(s, s_prime, vd, cluster, controller_id, msg);
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

#[verifier(rlimit(100))]
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
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    n > 0
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
            no_pending_req_in_cluster(vd, controller_id),
            etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
            pending_scale_old_vrs_req_in_flight(vd.object_ref(), controller_id, nv_uid_key.0),
            etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        pending_scale_old_vrs_req_in_flight(vd.object_ref(), controller_id, nv_uid_key.0),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
    let input = (None::<Message>, Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_local_state_validity_and_coherence(s, s_prime, vd, cluster, controller_id, msg);
                lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                    s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n
                );
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == None::<Message> && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    VReplicaSetView::marshal_preserves_integrity();
                    assert(pending_scale_old_vrs_req_in_flight(vd.object_ref(), controller_id, nv_uid_key.0)(s_prime)) by {
                        let req_msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                        let req = req_msg.content.get_APIRequest_0().get_GetThenUpdateRequest_0();
                        let key = req.key();
                        let vds_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
                        assert forall |i: int| #![trigger vds_prime.old_vrs_list[i]] 0 <= i < vds_prime.old_vrs_index
                            implies vds_prime.old_vrs_list[i].object_ref() != key by {
                            assert(key == vds_prime.old_vrs_list[vds_prime.old_vrs_index as int].object_ref());
                            if vds_prime.old_vrs_list[i].object_ref() == key {
                                let key_list = vds_prime.old_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref());
                                assert(key_list[i] == key_list[vds_prime.old_vrs_index as int]);
                                assert(!key_list.no_duplicates());
                                assert(false);
                            }
                        }
                    }
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
#[verifier(spinoff_prover)]
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
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    n > 0
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
            resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd.object_ref(), controller_id, resp_msg, nv_uid_key.0),
            etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
            pending_scale_old_vrs_req_in_flight(vd.object_ref(), controller_id, nv_uid_key.0),
            etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd.object_ref(), controller_id, resp_msg, nv_uid_key.0),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        pending_scale_old_vrs_req_in_flight(vd.object_ref(), controller_id, nv_uid_key.0),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
                lemma_api_request_other_than_pending_req_msg_maintains_local_state_validity_and_coherence(s, s_prime, vd, cluster, controller_id, msg);
                lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                    s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n
                );
                lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
                    s, s_prime, vd, cluster, controller_id, msg
                );
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == Some(resp_msg) && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    VReplicaSetView::marshal_preserves_integrity();
                    assert(pending_scale_old_vrs_req_in_flight(vd.object_ref(), controller_id, nv_uid_key.0)(s_prime)) by {
                        let req_msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                        let req = req_msg.content.get_APIRequest_0().get_GetThenUpdateRequest_0();
                        let key = req.key();
                        let vds_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
                        assert forall |i: int| #![trigger vds_prime.old_vrs_list[i]] 0 <= i < vds_prime.old_vrs_index
                            implies vds_prime.old_vrs_list[i].object_ref() != key by {
                            assert(key == vds_prime.old_vrs_list[vds_prime.old_vrs_index as int].object_ref());
                            if vds_prime.old_vrs_list[i].object_ref() == key {
                                let key_list = vds_prime.old_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref());
                                assert(key_list[i] == key_list[vds_prime.old_vrs_index as int]);
                                assert(!key_list.no_duplicates());
                                assert(false);
                            }
                        }
                    }
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
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    n > 0,
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
            req_msg_is_pending_scale_old_vrs_req_in_flight(vd.object_ref(), controller_id, req_msg, nv_uid_key.0),
            etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
            exists_resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd.object_ref(), controller_id, nv_uid_key.0),
            etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
            local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        req_msg_is_pending_scale_old_vrs_req_in_flight(vd.object_ref(), controller_id, req_msg, nv_uid_key.0),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        exists_resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd.object_ref(), controller_id, nv_uid_key.0),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                if input->0 == req_msg {
                    let resp_msg = lemma_scale_old_vrs_req_returns_ok(s, s_prime, vd, cluster, controller_id, req_msg, nv_uid_key, n);
                    VReplicaSetView::marshal_preserves_integrity();
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                    });
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    assert(etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), (n - 1) as nat)(s_prime));
                    assert(local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), (n - 1) as nat)(s_prime));
                    assert(local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)(s_prime));
                } else {
                    let msg = input->0;
                    lemma_api_request_other_than_pending_req_msg_maintains_local_state_validity_and_coherence(s, s_prime, vd, cluster, controller_id, msg);
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
                    // etcd object is not touched by other msg
                    let key = req_msg.content.get_APIRequest_0().get_GetThenUpdateRequest_0().key();
                    lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, msg
                    );
                    assert(s_prime.in_flight().contains(req_msg));
                }
            },
            _ => {}
        }
    }
    let input = Some(req_msg);
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let msg = input->0;
        let resp_msg = lemma_scale_old_vrs_req_returns_ok(s, s_prime, vd, cluster, controller_id, msg, nv_uid_key, n);
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
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    n > 0
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
            exists_resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd.object_ref(), controller_id, nv_uid_key.0),
            etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
            exists_resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd.object_ref(), controller_id, nv_uid_key.0),
            etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
            local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        )))),
{
    let scale_resp = |n: nat| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        exists_resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd.object_ref(), controller_id, nv_uid_key.0),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
    ));
    let scale_resp_msg = |msg: Message, n: nat| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd.object_ref(), controller_id, msg, nv_uid_key.0),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
    ));
    let scale_req = |n: nat| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        pending_scale_old_vrs_req_in_flight(vd.object_ref(), controller_id, nv_uid_key.0),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
    ));
    let scale_req_msg = |msg: Message, n: nat| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        req_msg_is_pending_scale_old_vrs_req_in_flight(vd.object_ref(), controller_id, msg, nv_uid_key.0),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n - nat1!()),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
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
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    n == 0,
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
            no_pending_req_in_cluster(vd, controller_id),
            etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step!(Done)),
            no_pending_req_in_cluster(vd, controller_id),
            current_state_matches(vd)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS]),
        no_pending_req_in_cluster(vd, controller_id),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Done]),
        no_pending_req_in_cluster(vd, controller_id),
        current_state_matches(vd)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(cluster, controller_id)(s)
    };
    always_to_always_later(spec, lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)));
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
        later(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))
    );
    let input = (None, Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_local_state_validity_and_coherence(s, s_prime, vd, cluster, controller_id, msg);
                lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                    s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n
                );
                // trigger
                assert(s.in_flight().contains(msg));
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == None::<Message> && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    lemma_esr_equiv_to_instantiated_etcd_state_is(vd, cluster, controller_id, s_prime);
                }
            },
            _ => {}
        }
    }
    // without this proof will fail
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime)  by {
        VDeploymentReconcileState::marshal_preserves_integrity();
        lemma_esr_equiv_to_instantiated_etcd_state_is(vd, cluster, controller_id, s_prime);
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

#[verifier(rlimit(100))]
#[verifier(spinoff_prover)]
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
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
ensures
    spec.entails(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
            resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd.object_ref(), controller_id, resp_msg, nv_uid_key.0),
            etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!()),
            local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!()),
            local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vd_step_with_vd(vd, controller_id, at_step![Done]),
            no_pending_req_in_cluster(vd, controller_id),
            current_state_matches(vd)
        )))),
{
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS]),
        resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd.object_ref(), controller_id, resp_msg, nv_uid_key.0),
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!()),
        local_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!()),
        local_state_is_valid_and_coherent_with_etcd(vd.object_ref(), controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Done]),
        no_pending_req_in_cluster(vd, controller_id),
        current_state_matches(vd)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(cluster, controller_id)(s)
    };
    always_to_always_later(spec, lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)));
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
        later(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))
    );
    let input = (Some(resp_msg), Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_local_state_validity_and_coherence(s, s_prime, vd, cluster, controller_id, msg);
                lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                    s, s_prime, vd, cluster, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), nat0!()
                );
                lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
                    s, s_prime, vd, cluster, controller_id, msg
                );
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.1 == Some(resp_msg) && input.2 == Some(vd.object_ref()) {
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    lemma_esr_equiv_to_instantiated_etcd_state_is(vd, cluster, controller_id, s_prime);
                }
            },
            _ => {}
        }
    }
    // without this the proof will be 1s slower
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime)  by {
        VDeploymentReconcileState::marshal_preserves_integrity();
        lemma_esr_equiv_to_instantiated_etcd_state_is(vd, cluster, controller_id, s_prime);
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

// From lemma_from_init_to_current_state_matches, we know the final state is
// final = at_vd_step_with_vd(.., at_step![Done]) && no_pending_req_in_cluster(..) && current_state_matches(..)
// We need to construct a reachable closure predicate where:
// P -> []P
// final |= P
// P |= ESR (ESR = current_state_matches(vd))
pub proof fn lemma_current_state_matches_is_stable(
    spec: TempPred<ClusterState>, vd: VDeploymentView, p: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    // spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    spec.entails(p.leads_to(lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Done]),
        no_pending_req_in_cluster(vd, controller_id),
        current_state_matches(vd)
    )))),
ensures
    spec.entails(p.leads_to(always(lift_state(current_state_matches(vd))))),
{
    // ESR -> etcd_state_is (which is easier to reason about)
    let final_state = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Done]),
        no_pending_req_in_cluster(vd, controller_id),
        current_state_matches(vd)
    );
    let final_state_with_instantiated_nv = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Done]),
        no_pending_req_in_cluster(vd, controller_id),
        current_state_matches(vd),
        instantiated_etcd_state_is_with_zero_old_vrs(vd.object_ref(), controller_id)
    );
    assert(lift_state(final_state).entails(lift_state(final_state_with_instantiated_nv))) by {
        assert forall |ex: Execution<ClusterState>| lift_state(final_state).satisfied_by(ex)
            implies lift_state(final_state_with_instantiated_nv).satisfied_by(ex) by {
            let s = ex.head();
            lemma_esr_equiv_to_instantiated_etcd_state_is(vd, cluster, controller_id, s);
        }
    }
    temp_pred_equality(lift_state(final_state), lift_state(final_state_with_instantiated_nv));
    let inv_after_esr = |s: ClusterState| {
        &&& current_state_matches(vd)(s)
        &&& instantiated_etcd_state_is_with_zero_old_vrs(vd.object_ref(), controller_id)(s)
        &&& s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()) ==> {
            ||| at_vd_step_with_vd(vd, controller_id, at_step![Init])(s)
            ||| at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s)
            ||| at_vd_step_with_vd(vd, controller_id, at_step![AfterCreateNewVRS])(s)
            ||| at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS])(s)
            ||| at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS])(s)
            ||| at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleDownOldVRS])(s)
        }
        &&& if at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s) {
            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
            &&& s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg is Some
            &&& req_msg_is_list_vrs_req(vd.object_ref(), controller_id, req_msg, s)
            &&& forall |msg| {
                &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
                &&& #[trigger] s.in_flight().contains(msg)
                &&& resp_msg_matches_req_msg(msg, req_msg)
            } ==> resp_msg_is_ok_list_resp_containing_matched_vrs(vd.object_ref(), controller_id, msg, s)
        } else{
            s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg is None
        }
    };
    entails_implies_leads_to(spec, lift_state(final_state), lift_state(inv_after_esr));
    leads_to_trans(spec, p, lift_state(final_state), lift_state(inv_after_esr));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& helper_invariants::cr_in_reconciles_has_the_same_spec_uid_name_and_namespace_as_vd(vd, controller_id)(s_prime)
        &&& helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(cluster, controller_id)(s)
    };
    always_to_always_later(spec, lift_state(helper_invariants::cr_in_reconciles_has_the_same_spec_uid_name_and_namespace_as_vd(vd, controller_id)));
    vd_rely_condition_equivalent_to_lifted_vd_rely_condition_action(spec, cluster, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)),
        lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VDeploymentView>(controller_id)),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)),
        lift_state(Cluster::desired_state_is(vd)),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vd.object_ref())),
        lift_state(Cluster::etcd_object_has_lower_uid_than_uid_counter()),
        lift_state(helper_invariants::no_other_pending_request_interferes_with_vd_reconcile(vd, controller_id)),
        lift_state(helper_invariants::garbage_collector_does_not_delete_vd_vrs_objects(vd)),
        lift_state(helper_invariants::every_msg_from_vd_controller_carries_vd_key(controller_id)),
        lift_state(helper_invariants::vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)),
        lift_state(helper_invariants::no_pending_mutation_request_not_from_controller_on_vrs_objects()),
        lift_state(helper_invariants::cr_in_reconciles_has_the_same_spec_uid_name_and_namespace_as_vd(vd, controller_id)),
        later(lift_state(helper_invariants::cr_in_reconciles_has_the_same_spec_uid_name_and_namespace_as_vd(vd, controller_id))),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition(cluster, controller_id)
    );
    assert forall |s, s_prime: ClusterState| inv_after_esr(s) && #[trigger] stronger_next(s, s_prime) implies inv_after_esr(s_prime) by {
        VReplicaSetView::marshal_preserves_integrity();
        VDeploymentView::marshal_preserves_integrity();
        VDeploymentReconcileState::marshal_preserves_integrity();
        let step = choose |step| cluster.next_step(s, s_prime, step);
        let (uid, key) = choose |nv_uid_key: (Uid, ObjectRef)| #![trigger dummy(nv_uid_key)] {
            let vd = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
            &&& etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(1))), 0)(s)
        };
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                let new_msgs = s_prime.in_flight().sub(s.in_flight());
                if s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()) {
                    if !Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), msg) {
                        lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                            s, s_prime, vd, cluster, controller_id, msg, Some((uid, key, vd.spec.replicas.unwrap_or(1))), 0
                        );
                        // Maintain quantified invariant.
                        if at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s) {
                            let req_msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                            assert forall |msg| {
                                &&& inv_after_esr(s)
                                &&& stronger_next(s, s_prime)
                                &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
                                &&& #[trigger] s.in_flight().contains(msg)
                                &&& resp_msg_matches_req_msg(msg, req_msg)
                            } implies resp_msg_is_ok_list_resp_containing_matched_vrs(vd.object_ref(), controller_id, msg, s) by {
                                assert(forall |msg| #[trigger] new_msgs.contains(msg) ==> !(#[trigger] resp_msg_matches_req_msg(msg, req_msg)));
                                if !new_msgs.contains(msg) {
                                    assert(s.in_flight().contains(msg));
                                }
                            }
                        }
                    } else {
                        if at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s) {
                            let req_msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                            assert forall |msg| {
                                &&& inv_after_esr(s)
                                &&& stronger_next(s, s_prime)
                                &&& #[trigger] s_prime.in_flight().contains(msg)
                                &&& msg.src.is_APIServer()
                                &&& resp_msg_matches_req_msg(msg, req_msg)
                            } implies resp_msg_is_ok_list_resp_containing_matched_vrs(vd.object_ref(), controller_id, msg, s) by {
                                if !new_msgs.contains(msg) {
                                    assert(s.in_flight().contains(msg));
                                } else {
                                    lemma_list_vrs_request_returns_ok_with_objs_matching_vd(
                                        s, s_prime, vd, cluster, controller_id, req_msg,
                                    );
                                }
                            }
                        }
                    }
                } else {
                    lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
                        s, s_prime, vd, cluster, controller_id, msg, Some((uid, key, vd.spec.replicas.unwrap_or(1))), 0
                    );
                }
            },
            Step::ControllerStep(input) => {
                if s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
                    && input.0 == controller_id
                    && input.2 == Some(vd.object_ref()) {
                    let resp_msg = input.1->0;
                    if at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s) {
                        lemma_from_list_resp_to_next_state(
                            s, s_prime, vd, cluster, controller_id, resp_msg, Some((uid, key, vd.spec.replicas.unwrap_or(1))), 0
                        );
                    }
                    if at_vd_step_with_vd(vd, controller_id, at_step![Init])(s) {
                         // prove that the newly sent message has no response.
                         if s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg is Some {
                            let req_msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                            assert(forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id);
                            assert(s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg));
                            assert forall |msg| #[trigger] s_prime.in_flight().contains(msg)
                                && (forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id)
                                && s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg)
                                && msg != req_msg
                                implies msg.rpc_id != req_msg.rpc_id by {
                                if !s.in_flight().contains(msg) {} // need this to invoke trigger.
                            }
                        }
                    }
                } else if !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()) {}
            },
            _ => {
                let new_msgs = s_prime.in_flight().sub(s.in_flight());
                // Maintain quantified invariant.
                if at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s) {
                    let req_msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                    assert forall |msg| {
                        &&& inv_after_esr(s)
                        &&& stronger_next(s, s_prime)
                        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
                        &&& #[trigger] s.in_flight().contains(msg)
                        &&& resp_msg_matches_req_msg(msg, req_msg)
                    } implies resp_msg_is_ok_list_resp_containing_matched_vrs(vd.object_ref(), controller_id, msg, s) by {
                        assert(forall |msg| #[trigger] new_msgs.contains(msg) ==> !(#[trigger] resp_msg_matches_req_msg(msg, req_msg)));
                        if !new_msgs.contains(msg) {
                            assert(s.in_flight().contains(msg));
                        }
                    }
                }
            }
        }
    }
    leads_to_stable(spec, lift_action(stronger_next), p, lift_state(inv_after_esr));
    leads_to_always_enhance(spec, true_pred(), p, lift_state(inv_after_esr), lift_state(current_state_matches(vd)));
}

// Havoc function for VDeploymentView.
uninterp spec fn make_vd() -> VDeploymentView;

}