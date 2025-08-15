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
use vstd::{seq_lib::*, prelude::*};
use crate::vstd_ext::seq_lib::*;

verus! {

pub proof fn lemma_list_vrs_request_returns_ok_with_objs_matching_vd(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    msg: Message,
) -> (resp_msg: Message)
requires
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    req_msg_is_list_vrs_req(vd, controller_id, msg),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
ensures
    resp_msg == handle_list_request_msg(msg, s.api_server).1,
    resp_msg_is_ok_list_resp_containing_matched_vrs(s_prime, vd, resp_msg),
{
    let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
    // TODO: weaken at_vd_step_with_vd
    assert(triggering_cr.metadata == vd.metadata);
    assert(triggering_cr.object_ref() == vd.object_ref());
    let resp_msg = handle_list_request_msg(msg, s.api_server).1;
    assert(resp_msg_is_ok_list_resp_containing_matched_vrs(s_prime, vd, resp_msg)) by {
        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
        let vrs_list = objects_to_vrs_list(resp_objs).unwrap();
        assert(resp_msg.content.is_list_response());
        assert(resp_msg.content.get_list_response().res is Ok);
        assert(resp_objs == s.resources().values().filter(list_vrs_obj_filter(vd.metadata.namespace)).to_seq());
        assert(objects_to_vrs_list(resp_objs) is Some);
        assert(resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref()).no_duplicates());
        assert(filter_old_and_new_vrs(vd, vrs_list.filter(|vrs| valid_owned_object(vrs, vd))) == filter_old_and_new_vrs_on_etcd(vd, s_prime.resources()));
        assert forall |obj| #[trigger] resp_objs.contains(obj) implies {
            &&& VReplicaSetView::unmarshal(obj) is Ok
            &&& obj.kind == VReplicaSetView::kind()
            &&& obj.metadata.namespace == vd.metadata.namespace
            &&& obj.metadata.owner_references is Some
            &&& obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
            &&& s_prime.resources().contains_key(obj.object_ref())
            &&& s_prime.resources()[obj.object_ref()] == obj
        } by {
            assert(VReplicaSetView::unmarshal(obj) is Ok);
            assert(obj.kind == VReplicaSetView::kind());
            assert(obj.metadata.namespace == vd.metadata.namespace);
            assert(obj.metadata.owner_references is Some);
            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]);
            assert(s_prime.resources().contains_key(obj.object_ref()));
            assert(s_prime.resources()[obj.object_ref()] == obj);
        }
    }
    return resp_msg;
}

#[verifier(external_body)]
pub proof fn lemma_create_new_vrs_request_returns_ok_after_ensure_new_vrs(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    msg: Message, old_vrs_index: nat
) -> (resp_msg: Message)
requires
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    req_msg_is_pending_create_new_vrs_req_in_flight(vd, controller_id, msg)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    etcd_state_is(vd, controller_id, None, old_vrs_index)(s),
    local_state_is_valid_and_coherent(vd, controller_id)(s),
ensures
    resp_msg == handle_create_request_msg(cluster.installed_types, msg, s.api_server).1,
    resp_msg_is_ok_create_new_vrs_resp(vd, controller_id, resp_msg)(s_prime),
    etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), old_vrs_index)(s_prime),
    local_state_is_valid_and_coherent(vd, controller_id)(s_prime),
{
    return handle_create_request_msg(cluster.installed_types, msg, s.api_server).1;
}

#[verifier(external_body)]
pub proof fn lemma_get_then_update_request_returns_ok_after_scale_new_vrs(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    msg: Message, replicas: int, old_vrs_index: nat
) -> (resp_msg: Message)
requires
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    req_msg_is_scale_new_vrs_req(vd, controller_id, msg)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    etcd_state_is(vd, controller_id, Some(replicas), old_vrs_index)(s),
    local_state_is_valid_and_coherent(vd, controller_id)(s),
ensures
    resp_msg == handle_get_then_update_request_msg(cluster.installed_types, msg, s.api_server).1,
    resp_msg_is_ok_get_then_update_resp(vd, controller_id, resp_msg)(s_prime),
    etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), old_vrs_index)(s_prime),
    local_state_is_valid_and_coherent(vd, controller_id)(s_prime),
{
    return handle_get_then_update_request_msg(cluster.installed_types, msg, s.api_server).1;
}

#[verifier(external_body)]
pub proof fn lemma_get_then_update_request_returns_ok_after_scale_down_old_vrs(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    msg: Message, old_vrs_index: nat
) -> (resp_msg: Message)
requires
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    req_msg_is_scale_down_old_vrs_req(vd, controller_id, msg)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), old_vrs_index)(s),
    local_state_is_valid_and_coherent(vd, controller_id)(s),
ensures
    resp_msg == handle_get_then_update_request_msg(cluster.installed_types, msg, s.api_server).1,
    resp_msg_is_ok_get_then_update_resp(vd, controller_id, resp_msg)(s_prime),
    etcd_state_is(vd, controller_id, Some(vd.spec.replicas.unwrap_or(int1!())), (old_vrs_index - nat1!()) as nat)(s_prime),
    local_state_is_valid_and_coherent(vd, controller_id)(s_prime),
{
    return handle_get_then_update_request_msg(cluster.installed_types, msg, s.api_server).1;
}

#[verifier(external_body)]
pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    msg: Message,
)
requires
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
    // first, prove filter_old_and_new_vrs_on_etc(s) == filter_old_and_new_vrs_on_etcd(s_prime)
    let objs = s.resources().values().filter(list_vrs_obj_filter(vd.metadata.namespace)).to_seq();
    let filtered_vrs_list = objects_to_vrs_list(objs).unwrap().filter(|vrs: VReplicaSetView| valid_owned_object(vrs, vd));
    let (new_vrs, old_vrs_list) = filter_old_and_new_vrs_on_etcd(vd, s.resources());
    let objs_prime = s_prime.resources().values().filter(list_vrs_obj_filter(vd.metadata.namespace)).to_seq();
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
                    _ => {},
                }
            }
        }
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
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
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