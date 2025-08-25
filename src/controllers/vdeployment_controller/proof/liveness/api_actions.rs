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
    proof::{predicate::*, helper_invariants},
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use crate::reconciler::spec::io::*;
use vstd::{seq_lib::*, prelude::*, map_lib::*};
use crate::vstd_ext::{seq_lib::*, set_lib::*};

verus! {

pub proof fn lemma_list_vrs_request_returns_ok_with_objs_matching_vd(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    req_msg: Message,
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    req_msg_is_list_vrs_req(vd, controller_id, req_msg),
    at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
ensures
    resp_msg == handle_list_request_msg(req_msg, s.api_server).1,
    resp_msg_is_ok_list_resp_containing_matched_vrs(
        s_prime, VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap(), resp_msg
    ),
{
    broadcast use group_seq_properties;
    let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
    let req = req_msg.content.get_list_request();
    let list_req_filter = |o: DynamicObjectView| {
        // why changing the order of fields makes a difference
        &&& o.object_ref().namespace == req.namespace
        &&& o.object_ref().kind == req.kind
    }; 
    let resp_msg = handle_list_request_msg(req_msg, s.api_server).1;
    assert(resp_msg_is_ok_list_resp_containing_matched_vrs(s_prime, triggering_cr, resp_msg)) by {
        assert(triggering_cr.metadata.namespace is Some);
        assert(req.kind == VReplicaSetView::kind());
        assert(req.namespace == triggering_cr.metadata.namespace->0);
        assert(resp_msg.content.is_list_response());
        assert(resp_msg.content.get_list_response() == handle_list_request(req, s.api_server));
        assert(resp_msg.content.get_list_response().res is Ok);
        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
        assert(resp_objs == s.resources().values().filter(list_req_filter).to_seq());
        assert forall |o| #[trigger] resp_objs.contains(o) implies {
            &&& o.kind == VReplicaSetView::kind()
            &&& o.metadata.namespace == triggering_cr.metadata.namespace
            &&& VReplicaSetView::unmarshal(o) is Ok
            &&& s_prime.resources().contains_key(o.object_ref())
            &&& s_prime.resources()[o.object_ref()] == o
        } by {
            assert(s.resources().values().filter(list_req_filter).contains(o)) by {
                lemma_values_finite(s.resources());
                finite_set_to_seq_contains_all_set_elements(s.resources().values().filter(list_req_filter));
            }
            assert(list_req_filter(o));
            assert(s.resources().contains_key(o.object_ref()));
            assert(s.resources()[o.object_ref()] == o);
        }
        assert(objects_to_vrs_list(resp_objs) is Some) by {
            seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(resp_objs, |o: DynamicObjectView| VReplicaSetView::unmarshal(o).is_err());
        }
        assert(resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref()).no_duplicates()) by {
            lemma_values_finite(s.resources());
            finite_set_to_seq_has_no_duplicates(s.resources().values().filter(list_req_filter));
            // now we know resp_objs has no duplicates, prove keys are unique by contradiction
            assert forall|i, j| (0 <= i < resp_objs.len() && 0 <= j < resp_objs.len() && i != j) implies #[trigger] resp_objs[i].object_ref() != #[trigger] resp_objs[j].object_ref() by {
                if resp_objs[i].object_ref() == resp_objs[j].object_ref() {
                    // trigger of s.resources()[o.object_ref()] == o
                    assert(resp_objs.contains(resp_objs[i]));
                    assert(resp_objs.contains(resp_objs[j]));
                    assert(resp_objs[i] == resp_objs[j]);
                }
            }
        }
    }
    return resp_msg;
}

#[verifier(external_body)]
// staged, we need to handle collision
pub proof fn lemma_create_new_vrs_request_returns_ok_after_ensure_new_vrs(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    req_msg: Message, old_vrs_index: nat
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    req_msg_is_pending_create_new_vrs_req_in_flight(vd, controller_id, req_msg)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    etcd_state_is(vd, controller_id, None, old_vrs_index)(s),
    local_state_is_valid_and_coherent(vd, controller_id)(s),
ensures
    resp_msg == handle_create_request_msg(cluster.installed_types, req_msg, s.api_server).1,
    resp_msg_is_ok_create_new_vrs_resp(vd, controller_id, resp_msg)(s_prime),
    etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), old_vrs_index)(s_prime),
    local_state_is_valid_and_coherent(vd, controller_id)(s_prime),
{
    broadcast use group_seq_properties;
    let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
    let request = req_msg.content.get_APIRequest_0().get_CreateRequest_0();
    let new_vrs = make_replica_set(triggering_cr);
    assert(request == CreateRequest {
        namespace: triggering_cr.metadata.namespace.unwrap(),
        obj: new_vrs.marshal()
    });
    assert(s_prime.api_server == handle_create_request_msg(cluster.installed_types, req_msg, s.api_server).0);
    assert(create_request_admission_check(cluster.installed_types, request, s.api_server) is None) by {
        VReplicaSetView::marshal_preserves_integrity();
    }
    assume(false);
    return handle_create_request_msg(cluster.installed_types, req_msg, s.api_server).1;
}

pub proof fn lemma_get_then_update_request_returns_ok_after_scale_new_vrs(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    req_msg: Message, replicas: int, old_vrs_index: nat
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    req_msg_is_scale_new_vrs_req(vd, controller_id, req_msg)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    etcd_state_is(vd, controller_id, Some(replicas), old_vrs_index)(s),
    local_state_is_valid_and_coherent(vd, controller_id)(s),
ensures
    resp_msg == handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).1,
    resp_msg_is_ok_get_then_update_resp(vd, controller_id, resp_msg)(s_prime),
    etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), old_vrs_index)(s_prime),
    local_state_is_valid_and_coherent(vd, controller_id)(s_prime),
{
    let req = req_msg.content.get_get_then_update_request();
    let etcd_obj = s.resources()[req.key()];
    // update can succeed
    assert(etcd_obj.metadata.owner_references_contains(req.owner_ref));
    assert(req.owner_ref == vd.controller_owner_ref());
    assert(s.resources().contains_key(req.key()));
    assert(s_prime.api_server == handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).0);
    assert(filter_old_and_new_vrs_on_etcd(vd, s_prime.resources()).0.is_Some());
    assume(false);
    return handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).1;
}

#[verifier(external_body)]
pub proof fn lemma_get_then_update_request_returns_ok_after_scale_down_old_vrs(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    req_msg: Message, old_vrs_index: nat
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    req_msg_is_scale_down_old_vrs_req(vd, controller_id, req_msg)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), old_vrs_index)(s),
    local_state_is_valid_and_coherent(vd, controller_id)(s),
ensures
    resp_msg == handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).1,
    resp_msg_is_ok_get_then_update_resp(vd, controller_id, resp_msg)(s_prime),
    etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), (old_vrs_index - nat1!()) as nat)(s_prime),
    local_state_is_valid_and_coherent(vd, controller_id)(s_prime),
{
    return handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).1;
}

pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    msg: Message,
)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    forall |vd| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s),
    vd_rely_condition(vd, cluster, controller_id)(s),
    (!Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), msg)
        || !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())),
ensures
    filter_old_and_new_vrs_on_etcd(vd, s.resources()) == filter_old_and_new_vrs_on_etcd(vd, s_prime.resources()),
    local_state_is_valid_and_coherent(vd, controller_id)(s) ==> local_state_is_valid_and_coherent(vd, controller_id)(s_prime),
{
    broadcast use group_seq_properties;
    // first, prove filter_old_and_new_vrs_on_etc(s) == filter_old_and_new_vrs_on_etcd(s_prime)
    let list_req_filter = |o: DynamicObjectView| {
        &&& o.object_ref().namespace == vd.metadata.namespace->0
        &&& o.object_ref().kind == VReplicaSetView::kind()
    }; 
    let objs = s.resources().values().filter(list_req_filter).to_seq();
    let filtered_vrs_list = objects_to_vrs_list(objs).unwrap().filter(|vrs: VReplicaSetView| valid_owned_object(vrs, vd));
    let (new_vrs, old_vrs_list) = filter_old_and_new_vrs_on_etcd(vd, s.resources());
    let objs_prime = s_prime.resources().values().filter(list_req_filter).to_seq();
    let filtered_vrs_list_prime = objects_to_vrs_list(objs_prime).unwrap().filter(|vrs: VReplicaSetView| valid_owned_object(vrs, vd));
    let (new_vrs_prime, old_vrs_list_prime) = filter_old_and_new_vrs_on_etcd(vd, s_prime.resources());
    assert forall |vrs| filtered_vrs_list.contains(vrs) implies filtered_vrs_list_prime.contains(vrs) by {
        assume({
            let etcd_obj = s.resources()[vrs.object_ref()];
            &&& s.resources().contains_key(vrs.object_ref())
            &&& VReplicaSetView::unmarshal(etcd_obj) is Ok
            &&& etcd_obj.metadata.namespace == vd.metadata.namespace
            &&& etcd_obj.metadata.owner_references is Some
            &&& etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
        });
        lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
            s, s_prime, vd, cluster, controller_id, vrs.object_ref(), msg
        );
        assume(filtered_vrs_list_prime.contains(vrs));
    }
    assert forall |vrs| filtered_vrs_list_prime.contains(vrs) implies filtered_vrs_list.contains(vrs) by {
        if !filtered_vrs_list.contains(vrs) {
            if msg.content.is_APIRequest() && msg.dst.is_APIServer() {
                match msg.src {
                    HostId::Controller(id, cr_key) => {
                        assume(false);
                    },
                    _ => {
                        assume(false);
                    },
                }
            }
        }
    }
    // we need to prove the order is preserved
    assert(filter_old_and_new_vrs_on_etcd(vd, s.resources()) == filter_old_and_new_vrs_on_etcd(vd, s_prime.resources())) by {
        assert(filter_old_and_new_vrs_on_etcd(vd, s.resources()) == filter_old_and_new_vrs(vd, filtered_vrs_list));
        assert(filter_old_and_new_vrs_on_etcd(vd, s_prime.resources()) == filter_old_and_new_vrs(vd, filtered_vrs_list_prime));
    }
    // second, prove local_state_is_valid_and_coherent(vd, controller_id)(s_prime)
    if local_state_is_valid_and_coherent(vd, controller_id)(s) {
        assume(false);
    }

}

// This lemma proves for all objects owned by vd (checked by namespace and owner_ref),
// the API request msg does not change or delete the object
// as the direct result of rely condition and non-interference property.
pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int,
    key: ObjectRef, msg: Message
)
requires
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    forall |vd| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s),
    vd_rely_condition(vd, cluster, controller_id)(s),
    // object in etcd is owned by vd
    ({
        let etcd_obj = s.resources()[key];
        &&& s.resources().contains_key(key)
        &&& VReplicaSetView::unmarshal(etcd_obj) is Ok
        &&& etcd_obj.metadata.namespace == vd.metadata.namespace
        &&& etcd_obj.metadata.owner_references is Some
        &&& etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
    }),
    // equal to msg.src != HostId::Controller(controller_id, vd.object_ref())
    (!Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), msg)
        || !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())),
ensures
    ({
        let etcd_obj = s.resources()[key];
        &&& s_prime.resources().contains_key(key)
        &&& etcd_obj == s_prime.resources()[key]
    }),
{
    assert(s.resources().contains_key(key));
    let etcd_obj = s.resources()[key];
    assert(VReplicaSetView::unmarshal(etcd_obj) is Ok);
    VReplicaSetView::marshal_preserves_integrity();
    // trigger rely condition,
    // rule out cases when etcd_obj get deleted with rely_delete and handle_delete_eq checks
    assert(etcd_obj.metadata.owner_references->0.contains(vd.controller_owner_ref())) by {
        broadcast use group_seq_properties;
        assert(etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]);
        seq_filter_contains_implies_seq_contains(etcd_obj.metadata.owner_references->0, controller_owner_filter(), vd.controller_owner_ref());
    }
    if msg.content.is_APIRequest() && msg.dst.is_APIServer() {
        match msg.src {
            HostId::Controller(id, cr_key) => {
                if id == controller_id {
                    assert(cr_key != vd.object_ref());
                    // same controller, other vd
                    // every_msg_from_vd_controller_carries_vd_key
                    let cr_key = msg.src.get_Controller_1();
                    let other_vd = VDeploymentView {
                        metadata: ObjectMetaView {
                            name: Some(cr_key.name),
                            namespace: Some(cr_key.namespace),
                            ..make_vd().metadata
                        },
                        ..make_vd()
                    };
                    // so msg can only be list, create or get_then_update
                    assert(helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, other_vd)(s));
                    match msg.content.get_APIRequest_0() {
                        APIRequest::DeleteRequest(req) => assert(false), // vd controller doesn't send delete req
                        APIRequest::GetThenDeleteRequest(req) => assert(false),
                        APIRequest::GetThenUpdateRequest(req) => {
                            assert(helper_invariants::no_other_pending_get_then_update_request_interferes_with_vd_reconcile(req, vd)(s));
                            assert(helper_invariants::vd_reconcile_get_then_update_request_only_interferes_with_itself(req, other_vd)(s));
                            // controller_owner_ref does not carry namespace, while object_ref does
                            // so object_ref != is not enough to prove controller_owner_ref !=
                            if cr_key.namespace == vd.metadata.namespace->0 {
                                assert(!etcd_obj.metadata.owner_references_contains(req.owner_ref)) by {
                                    if etcd_obj.metadata.owner_references_contains(req.owner_ref) {
                                        assert(req.owner_ref != vd.controller_owner_ref());
                                        assert(etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req.owner_ref));
                                    }
                                }
                            } // or else, namespace is different, so should not be touched at all
                        },
                        _ => {},
                    }
                    VDeploymentReconcileState::marshal_preserves_integrity();
                } else {
                    let other_id = msg.src.get_Controller_0();
                    // by every_in_flight_req_msg_from_controller_has_valid_controller_id, used by vd_rely
                    assert(cluster.controller_models.contains_key(other_id));
                    assert(vd_rely(other_id)(s)); // trigger vd_rely_condition
                    VDeploymentReconcileState::marshal_preserves_integrity();
                    match msg.content.get_APIRequest_0() {
                        APIRequest::DeleteRequest(req) => {},
                        APIRequest::GetThenDeleteRequest(req) => {
                            if req.key.kind == VReplicaSetView::kind() {
                                assert(!etcd_obj.metadata.owner_references_contains(req.owner_ref)) by {
                                    if etcd_obj.metadata.owner_references_contains(req.owner_ref) {
                                        assert(req.owner_ref != vd.controller_owner_ref());
                                        assert(etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req.owner_ref));
                                    }
                                }
                            }
                        },
                        APIRequest::GetThenUpdateRequest(req) => {
                            if req.obj.kind == VReplicaSetView::kind() {
                                // rely condition
                                assert({
                                    &&& req.owner_ref.controller is Some
                                    &&& req.owner_ref.controller->0
                                    &&& req.owner_ref.kind != VDeploymentView::kind()
                                });
                                assert(!etcd_obj.metadata.owner_references_contains(req.owner_ref)) by {
                                    if etcd_obj.metadata.owner_references_contains(req.owner_ref) {
                                        assert(req.owner_ref != vd.controller_owner_ref());
                                        assert(etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req.owner_ref));
                                    }
                                }
                            }
                        },
                        _ => {},
                    }
                }
            },
            _ => {},
        }
    }
}

// Havoc function for VDeploymentView.
uninterp spec fn make_vd() -> VDeploymentView;

}