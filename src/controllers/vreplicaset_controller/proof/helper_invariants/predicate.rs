// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::InstalledTypes}, 
    cluster::*, 
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    trusted::{
        liveness_theorem::*, 
        rely_guarantee::*, 
        spec_types::*, 
        step::*
    },
    proof::{predicate::*},
};
use vstd::prelude::*;

verus!{

// NOTE: helpers must be declared `pub open` for the main invariant to be declared so.

pub open spec fn no_other_pending_create_request_interferes_with_vrs_reconcile(
    req: CreateRequest,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == Kind::PodKind ==> !{
            let owner_references = req.obj.metadata.owner_references.get_Some_0();
            &&& req.obj.metadata.owner_references.is_Some()
            &&& owner_references.contains(vrs.controller_owner_ref())
        }
    }
}

pub open spec fn no_other_pending_update_request_interferes_with_vrs_reconcile(
    req: UpdateRequest,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == Kind::PodKind ==>
            req.obj.metadata.resource_version.is_Some()
            // Prevents 1): where a message not from our specific vrs updates
            // a vrs-owned pod.
            && !{
                let etcd_obj = s.resources()[req.key()];
                let owner_references = etcd_obj.metadata.owner_references.get_Some_0();
                &&& s.resources().contains_key(req.key())
                &&& etcd_obj.metadata.resource_version.is_Some()
                &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
                &&& etcd_obj.metadata.owner_references.is_Some()
                &&& owner_references.contains(vrs.controller_owner_ref())
            }
            // Prevents 2): where any message not from our specific vrs updates 
            // pods so they become owned by another VReplicaSet.
            && (req.obj.metadata.owner_references.is_Some() ==>
                        ! req.obj.metadata.owner_references.get_Some_0().contains(vrs.controller_owner_ref()))
    }
}

pub open spec fn no_other_pending_update_status_request_interferes_with_vrs_reconcile(
    req: UpdateStatusRequest,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == Kind::PodKind ==> 
            req.obj.metadata.resource_version.is_Some()
            && !{
                let etcd_obj = s.resources()[req.key()];
                let owner_references = etcd_obj.metadata.owner_references.get_Some_0();
                &&& s.resources().contains_key(req.key())
                &&& etcd_obj.metadata.resource_version.is_Some()
                &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
                &&& etcd_obj.metadata.owner_references.is_Some()
                &&& owner_references.contains(vrs.controller_owner_ref())
            }
    }
}

pub open spec fn no_other_pending_get_then_update_request_interferes_with_vrs_reconcile(
    req: GetThenUpdateRequest,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == Kind::PodKind ==> {
            // Prevents 1): where a message not from our specific vrs updates
            // a vrs-owned pod.
            &&& req.owner_ref.controller.is_Some()
            &&& req.owner_ref.controller.get_Some_0()
            &&& req.owner_ref != vrs.controller_owner_ref()
            // Prevents 2): where any message not from our specific vrs updates 
            // pods so they become owned by another VReplicaSet.
            &&& (req.obj.metadata.owner_references.is_Some() ==>
                    ! req.obj.metadata.owner_references.get_Some_0().contains(vrs.controller_owner_ref()))
        }
    }
}

pub open spec fn no_other_pending_delete_request_interferes_with_vrs_reconcile(
    req: DeleteRequest,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.key.kind == Kind::PodKind ==>
            req.preconditions.is_Some()
            && {
                ||| {
                    req.preconditions.get_Some_0().resource_version.is_Some()
                    && !{
                        let etcd_obj = s.resources()[req.key];
                        let owner_references = etcd_obj.metadata.owner_references.get_Some_0();
                        &&& s.resources().contains_key(req.key)
                        &&& etcd_obj.metadata.resource_version.is_Some()
                        &&& etcd_obj.metadata.resource_version
                            == req.preconditions.get_Some_0().resource_version
                        &&& etcd_obj.metadata.owner_references.is_Some()
                        &&& owner_references.contains(vrs.controller_owner_ref())
                    }
                }
                ||| { // required to handle garbage collector's messages.
                    &&& req.preconditions.unwrap().uid.is_Some()
                    &&& req.preconditions.unwrap().uid.unwrap() < s.api_server.uid_counter
                    &&& s.resources().contains_key(req.key)
                            ==> (!matching_pods(vrs, s.resources()).contains(s.resources()[req.key])
                                || s.resources()[req.key].metadata.uid.unwrap() > req.preconditions.unwrap().uid.unwrap())
                }
            }
    }
}

pub open spec fn no_other_pending_get_then_delete_request_interferes_with_vrs_reconcile(
    req: GetThenDeleteRequest,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.key.kind == Kind::PodKind ==> {
            &&& req.owner_ref.controller.is_Some()
            &&& req.owner_ref.controller.get_Some_0()
            &&& req.owner_ref != vrs.controller_owner_ref()
        }
    }
}

// States that no pending request that is not from the specific reconcile
// associated with `vrs` interferes with the reconcile of `vrs`.
pub open spec fn no_other_pending_request_interferes_with_vrs_reconcile(
    vrs: VReplicaSetView,
    controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src != HostId::Controller(controller_id, vrs.object_ref())
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        } ==> {
            let content = msg.content;
            match content.get_APIRequest_0() {
                APIRequest::CreateRequest(req) => no_other_pending_create_request_interferes_with_vrs_reconcile(req, vrs)(s),
                APIRequest::UpdateRequest(req) => no_other_pending_update_request_interferes_with_vrs_reconcile(req, vrs)(s),
                APIRequest::UpdateStatusRequest(req) => no_other_pending_update_status_request_interferes_with_vrs_reconcile(req, vrs)(s),
                APIRequest::GetThenUpdateRequest(req) => no_other_pending_get_then_update_request_interferes_with_vrs_reconcile(req, vrs)(s),
                APIRequest::DeleteRequest(req) => no_other_pending_delete_request_interferes_with_vrs_reconcile(req, vrs)(s),
                APIRequest::GetThenDeleteRequest(req) => no_other_pending_get_then_delete_request_interferes_with_vrs_reconcile(req, vrs)(s),
                _ => true,
            }
        }
    }
}

pub open spec fn vrs_reconcile_create_request_only_interferes_with_itself(
    req: CreateRequest,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let owner_references = req.obj.metadata.owner_references.get_Some_0();
        &&& req.obj.kind == Kind::PodKind
        &&& req.obj.metadata.owner_references.is_Some()
        &&& exists |owner_ref: OwnerReferenceView| {
            // using the macro messes up the trigger.
            &&& owner_references == #[trigger] Seq::empty().push(owner_ref)
            &&& owner_ref.controller.is_Some()
            &&& owner_ref.controller.get_Some_0()
            &&& owner_ref.kind == VReplicaSetView::kind()
            &&& owner_ref.name == vrs.object_ref().name
        }
    }
}

pub open spec fn vrs_reconcile_get_then_delete_request_only_interferes_with_itself(
    req: GetThenDeleteRequest,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& req.key.kind == Kind::PodKind
        &&& req.owner_ref.controller.is_Some()
        &&& req.owner_ref.controller.get_Some_0()
        &&& req.owner_ref.kind == VReplicaSetView::kind()
        &&& req.owner_ref.name == vrs.object_ref().name
    }
}

pub open spec fn vrs_reconcile_request_only_interferes_with_itself(
    controller_id: int,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content.is_APIRequest()
            &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
        } ==> match msg.content.get_APIRequest_0() {
            APIRequest::ListRequest(_) => true,
            APIRequest::CreateRequest(req) => vrs_reconcile_create_request_only_interferes_with_itself(req, vrs)(s),
            APIRequest::GetThenDeleteRequest(req) => vrs_reconcile_get_then_delete_request_only_interferes_with_itself(req, vrs)(s),
            _ => false, // vrs doesn't send other requests (yet).
        }
    }
}

// TODO: should not need to be a safety property.
pub open spec fn every_create_request_is_well_formed(cluster: Cluster, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #![trigger msg.dst.is_APIServer(), msg.content.is_APIRequest()] {
            let content = msg.content;
            let obj = content.get_create_request().obj;
            &&& s.in_flight().contains(msg)
            &&& msg.src.is_Controller()
            &&& msg.src.get_Controller_0() == controller_id
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
            &&& content.is_create_request()
        } ==> {
            let content = msg.content;
            let req = content.get_create_request();
            let obj = req.obj;
            let created_obj = DynamicObjectView {
                kind: req.obj.kind,
                metadata: ObjectMetaView {
                    // Set name for new object if name is not provided, here we generate
                    // a unique name. The uniqueness is guaranteed by generated_name_is_unique.
                    name: if req.obj.metadata.name.is_Some() {
                        req.obj.metadata.name
                    } else {
                        Some(generate_name(s.api_server))
                    },
                    namespace: Some(req.namespace), // Set namespace for new object
                    resource_version: Some(s.api_server.resource_version_counter), // Set rv for new object
                    uid: Some(s.api_server.uid_counter), // Set uid for new object
                    deletion_timestamp: None, // Unset deletion timestamp for new object
                    ..req.obj.metadata
                },
                spec: req.obj.spec,
                status: marshalled_default_status(req.obj.kind, cluster.installed_types), // Overwrite the status with the default one
            };
            &&& obj.metadata.name.is_None()
            &&& obj.metadata.deletion_timestamp.is_None()
            &&& created_obj.metadata.namespace.is_Some()
            &&& content.get_create_request().namespace == created_obj.metadata.namespace.unwrap()
            &&& unmarshallable_object(obj, cluster.installed_types)
            &&& created_object_validity_check(created_obj, cluster.installed_types).is_none()
            &&& PodView::unmarshal(created_obj).is_ok()
        }
    }
}

pub open spec fn no_pending_interfering_update_request() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        } ==> match msg.content.get_APIRequest_0() {
            APIRequest::UpdateRequest(req) => vrs_rely_update_req(req)(s),
            _ => true,
        }
    }
}

pub open spec fn no_pending_interfering_update_status_request() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        } ==> match msg.content.get_APIRequest_0() {
            APIRequest::UpdateStatusRequest(req) => vrs_rely_update_status_req(req)(s),
            _ => true,
        }
    }
}

pub open spec fn garbage_collector_does_not_delete_vrs_pods(vrs: VReplicaSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src.is_BuiltinController()
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        } ==> {
            let req = msg.content.get_delete_request(); 
            &&& msg.content.is_delete_request()
            &&& req.preconditions.is_Some()
            &&& req.preconditions.unwrap().uid.is_Some()
            &&& req.preconditions.unwrap().uid.unwrap() < s.api_server.uid_counter
            &&& s.resources().contains_key(req.key)
                    ==> (!matching_pods(vrs, s.resources()).contains(s.resources()[req.key])
                          || s.resources()[req.key].metadata.uid.unwrap() > req.preconditions.unwrap().uid.unwrap())
        }
    }
}

pub open spec fn no_pending_mutation_request_not_from_controller_on_pods() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& !(msg.src.is_Controller() || msg.src.is_BuiltinController())
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        } ==> {
            &&& msg.content.is_create_request() ==> msg.content.get_create_request().key().kind != PodView::kind()
            &&& msg.content.is_update_request() ==> msg.content.get_update_request().key().kind != PodView::kind()
            // too radical, loosen it later to allow updates on pod status.
            &&& msg.content.is_update_status_request() ==> msg.content.get_update_status_request().key().kind != PodView::kind()
            &&& msg.content.is_delete_request() ==> msg.content.get_delete_request().key.kind != PodView::kind()
            &&& msg.content.is_get_then_delete_request() ==> msg.content.get_get_then_delete_request().key.kind != PodView::kind()
            &&& msg.content.is_get_then_update_request() ==> msg.content.get_get_then_update_request().key().kind != PodView::kind()
        }
    }
}

pub open spec fn every_create_matching_pod_request_implies_at_after_create_pod_step(
    vrs: VReplicaSetView, installed_types: InstalledTypes, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #![trigger msg.dst.is_APIServer(), msg.content.is_APIRequest()] {
            let content = msg.content;
            let req = content.get_create_request();
            let created_obj = DynamicObjectView {
                kind: req.obj.kind,
                metadata: ObjectMetaView {
                    // Set name for new object if name is not provided, here we generate
                    // a unique name. The uniqueness is guaranteed by generated_name_is_unique.
                    name: if req.obj.metadata.name.is_Some() {
                        req.obj.metadata.name
                    } else {
                        Some(generate_name(s.api_server))
                    },
                    namespace: Some(req.namespace), // Set namespace for new object
                    resource_version: Some(s.api_server.resource_version_counter), // Set rv for new object
                    uid: Some(s.api_server.uid_counter), // Set uid for new object
                    deletion_timestamp: None, // Unset deletion timestamp for new object
                    ..req.obj.metadata
                },
                spec: req.obj.spec,
                status: marshalled_default_status(req.obj.kind, installed_types), // Overwrite the status with the default one
            };
            &&& s.in_flight().contains(msg)
            &&& msg.src.is_Controller()
            &&& msg.src.get_Controller_0() == controller_id
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
            &&& content.is_create_request()
            &&& owned_selector_match_is(vrs, created_obj)
        } ==> {
            // Need to modify these predicates.
            &&& exists |diff: nat| #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterCreatePod(diff))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        }
    }
}

pub open spec fn every_delete_matching_pod_request_implies_at_after_delete_pod_step(
    vrs: VReplicaSetView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #![trigger s.in_flight().contains(msg)] {
            let content = msg.content;
            let req = content.get_delete_request();
            let key = content.get_delete_request().key;
            let obj = s.resources()[key];
            &&& s.in_flight().contains(msg)
            &&& msg.src.is_Controller()
            &&& msg.src.get_Controller_0() == controller_id
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
            &&& content.is_delete_request()
            &&& s.resources().contains_key(key)
            &&& owned_selector_match_is(vrs, obj)
            // NOTE: We require that the resource version in etcd is
            // equal to the one carried by the delete request to
            // exclude the case where another reconcile working on another
            // vrs object tries to delete the same object.
            &&& req.preconditions.is_Some()
            &&& req.preconditions.unwrap().resource_version.is_Some()
            &&& req.preconditions.unwrap().uid.is_None()
            &&& obj.metadata.resource_version.is_Some()
            &&& obj.metadata.resource_version.unwrap() == 
                    req.preconditions.unwrap().resource_version.unwrap()
        } ==> {
            let content = msg.content;
            let req = content.get_delete_request();
            let obj = s.resources()[req.key];
            &&& exists |diff: nat| #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        }
    }
}

pub open spec fn each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            ==> {
                // Unlike the below invariant, this entire invariant is used in both proving itself as well as in other proofs.
                let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap();
                let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
                let filtered_pods = state.filtered_pods.unwrap();
                &&& triggering_cr.object_ref() == key
                &&& triggering_cr.metadata().well_formed_for_namespaced()
                &&& state.filtered_pods.is_Some() ==>
                // Maintained across deletes, 
                // maintained across creates since all new keys with generate_name
                // are unique, maintained across updates since there are
                // no updates.
                    forall |i| #![trigger filtered_pods[i]] 0 <= i < filtered_pods.len() ==>
                    (
                        filtered_pods[i].object_ref().namespace == triggering_cr.metadata.namespace.unwrap()
                        && ((s.resources().contains_key(filtered_pods[i].object_ref())
                                && s.resources()[filtered_pods[i].object_ref()].metadata.resource_version
                                    == filtered_pods[i].metadata.resource_version) ==>
                            (s.resources()[filtered_pods[i].object_ref()].metadata.owner_references_contains(
                                triggering_cr.controller_owner_ref()
                                )
                             ))
                        && filtered_pods[i].metadata.resource_version.is_some()
                        && filtered_pods[i].metadata.resource_version.unwrap()
                            < s.api_server.resource_version_counter
                    )
                // Special case: the above property holds on a list response to the
                // appropriate request. 
                &&& state.reconcile_step.is_AfterListPods() ==> {
                    let req_msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                    &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                    &&& req_msg.dst.is_APIServer()
                    &&& req_msg.content.is_list_request()
                    &&& req_msg.content.get_list_request() == ListRequest {
                        kind: PodView::kind(),
                        namespace: triggering_cr.metadata.namespace.unwrap(),
                    }
                    &&& forall |msg| {
                        let req_msg = s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.get_Some_0();
                        &&& #[trigger] s.in_flight().contains(msg)
                        &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                        &&& msg.src.is_APIServer()
                        &&& resp_msg_matches_req_msg(msg, req_msg)
                        &&& is_ok_resp(msg.content.get_APIResponse_0())
                    } ==> {
                        let resp_objs = msg.content.get_list_response().res.unwrap();
                        &&& msg.content.is_list_response()
                        &&& msg.content.get_list_response().res.is_Ok()
                        &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 
                        &&& forall |i| #![trigger resp_objs[i]] 0 <= i < resp_objs.len() ==>
                        (
                            resp_objs[i].metadata.namespace.is_some()
                            && resp_objs[i].metadata.namespace.unwrap() == triggering_cr.metadata.namespace.unwrap()
                            && ((s.resources().contains_key(resp_objs[i].object_ref())
                                    && s.resources()[resp_objs[i].object_ref()].metadata.resource_version
                                    == resp_objs[i].metadata.resource_version) ==> 
                                    s.resources()[resp_objs[i].object_ref()].metadata
                                        == resp_objs[i].metadata)
                            && resp_objs[i].metadata.resource_version.is_some()
                            && resp_objs[i].metadata.resource_version.unwrap()
                                    < s.api_server.resource_version_counter
                        )
                    }
                }
            }
    }
}
//
// TODO: See if we can split up this invariant into smaller ones.
// Both parts are necessary outside of this proof, but maybe for presentation purposes it 
// would be better to split them.
//

pub open spec fn at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(
    vrs: VReplicaSetView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) ==> {
            let key = vrs.object_ref();
            let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap();
            let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
            let filtered_pods = state.filtered_pods.unwrap();
            &&& triggering_cr.object_ref() == key
            &&& triggering_cr.metadata().well_formed_for_namespaced()
            // This portion of the predicate is used elsewhere throughout the proof: maintains an invariant on
            // local state as well as any delete requests sent by that controller.
            &&& forall |diff: nat| {
                #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s)
            } ==> {
                let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                let filtered_pods = state.filtered_pods.unwrap();
                let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
                let req_msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                &&& s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
                &&& VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).is_ok()
                &&& state.filtered_pods.is_Some()
                &&& diff <= filtered_pod_keys.len()
                &&& filtered_pod_keys.no_duplicates()
                &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                &&& req_msg.dst.is_APIServer()
                &&& req_msg.content.is_delete_request()
                &&& forall |i| #![trigger state.filtered_pods.unwrap()[i]] 0 <= i < diff ==> {
                    &&& s.resources().contains_key(filtered_pod_keys[i])
                    &&& matching_pods(vrs, s.resources()).contains(s.resources()[filtered_pod_keys[i]])
                    &&& PodView::unmarshal(s.resources()[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
                    &&& req_msg.content.get_delete_request().key != filtered_pod_keys[i]
                }
            }
            // This portion of the predicate is useful only in proving the invariant.
            &&& state.reconcile_step.is_AfterListPods() ==> {
                let req_msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                &&& req_msg.dst.is_APIServer()
                &&& req_msg.content.is_list_request()
                &&& req_msg.content.get_list_request() == ListRequest {
                    kind: PodView::kind(),
                    namespace: triggering_cr.metadata.namespace.unwrap(),
                }
                &&& forall |msg| {
                    let req_msg = s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.get_Some_0();
                    &&& #[trigger] s.in_flight().contains(msg)
                    &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                    &&& msg.src.is_APIServer()
                    &&& resp_msg_matches_req_msg(msg, req_msg)
                } ==> {
                    let resp_objs = msg.content.get_list_response().res.unwrap();
                    let resp_obj_keys = resp_objs.map_values(|o: DynamicObjectView| o.object_ref());
                    &&& msg.content.is_list_response()
                    &&& msg.content.get_list_response().res.is_Ok()
                    &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 
                    &&& resp_obj_keys.no_duplicates()
                    &&& matching_pods(vrs, s.resources()) == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
                    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
                }
            }
        }
    }
}
//
// TODO: See if we can write a more concise version of this invariant.
// Much of this predicate is not used in other proofs.
//

pub open spec fn every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(
    vrs: VReplicaSetView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #![trigger s.in_flight().contains(msg)] {
            let content = msg.content;
            let req = content.get_delete_request();
            &&& s.in_flight().contains(msg)
            &&& msg.src.is_Controller()
            &&& msg.src.get_Controller_0() == controller_id
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
            &&& content.is_delete_request()
        } ==> {
            let content = msg.content;
            let req = content.get_delete_request();
            &&& req.preconditions.is_Some()
            &&& req.preconditions.unwrap().resource_version.is_Some()
            &&& req.preconditions.unwrap().uid.is_None()
            &&& req.preconditions.unwrap().resource_version.unwrap() < s.api_server.resource_version_counter
        }
    }
}

pub open spec fn every_msg_from_vrs_controller_carries_vrs_key(
    controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #![trigger s.in_flight().contains(msg)] {
            let content = msg.content;
            &&& s.in_flight().contains(msg)
            &&& msg.src.is_Controller()
            &&& msg.src.get_Controller_0() == controller_id
        } ==> {
            msg.src.get_Controller_1().kind == VReplicaSetView::kind()
        }
    }
}

pub open spec fn vrs_in_etcd_does_not_have_deletion_timestamp(
    vrs: VReplicaSetView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| s.resources().contains_key(vrs.object_ref()) ==> {
        &&& s.resources()[vrs.object_ref()].metadata.deletion_timestamp.is_None()
        &&& VReplicaSetView::unmarshal(s.resources()[vrs.object_ref()]).unwrap().metadata().deletion_timestamp.is_None()
    }
}

pub open spec fn vrs_in_schedule_does_not_have_deletion_timestamp(
    vrs: VReplicaSetView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| s.scheduled_reconciles(controller_id).contains_key(vrs.object_ref()) ==> {
        &&& s.scheduled_reconciles(controller_id)[vrs.object_ref()].metadata.deletion_timestamp.is_None()
        &&& VReplicaSetView::unmarshal(s.scheduled_reconciles(controller_id)[vrs.object_ref()]).unwrap().metadata().deletion_timestamp.is_None()
    }
}

pub open spec fn vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(
    vrs: VReplicaSetView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) ==> {
        &&& s.ongoing_reconciles(controller_id)[vrs.object_ref()].triggering_cr.metadata.deletion_timestamp.is_None()
        &&& VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].triggering_cr).unwrap().metadata().deletion_timestamp.is_None()
    }
}

}