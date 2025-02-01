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
    trusted::{liveness_theorem::*, spec_types::*, step::*},
    proof::{predicate::*},
};
use vstd::prelude::*;

verus!{

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
            &&& obj.metadata.deletion_timestamp.is_None()
            &&& created_obj.metadata.namespace.is_Some()
            &&& content.get_create_request().namespace == created_obj.metadata.namespace.unwrap()
            &&& unmarshallable_object(obj, cluster.installed_types)
            &&& created_object_validity_check(created_obj, cluster.installed_types).is_none()
            &&& PodView::unmarshal(created_obj).is_ok()
        }
    }
}

pub open spec fn no_pending_update_or_update_status_request_on_pods() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        } ==> {
            &&& msg.content.is_update_request() ==> msg.content.get_update_request().key().kind != PodView::kind()
            &&& msg.content.is_update_status_request() ==> msg.content.get_update_status_request().key().kind != PodView::kind()
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
                    ==> (!matching_pod_entries(vrs, s.resources()).contains_key(req.key)
                          || s.resources()[req.key].metadata.uid.unwrap() > req.preconditions.unwrap().uid.unwrap())
        }
    }
}

pub open spec fn no_pending_create_or_delete_request_not_from_controller_on_pods() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& !(msg.src.is_Controller() || msg.src.is_BuiltinController())
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        } ==> {
            &&& msg.content.is_create_request() ==> msg.content.get_create_request().key().kind != PodView::kind()
            &&& msg.content.is_delete_request() ==> msg.content.get_delete_request().key.kind != PodView::kind()
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
                let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap();
                let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
                let filtered_pods = state.filtered_pods.unwrap();
                &&& triggering_cr.object_ref() == key
                &&& triggering_cr.metadata().well_formed()
                &&& state.filtered_pods.is_Some() ==>
                // Maintained across deletes, 
                // maintained across creates since all new keys with generate_name
                // are unique, maintained across updates since there are
                // no updates.
                    forall |i| #![auto] 0 <= i < filtered_pods.len() ==>
                    (
                        filtered_pods[i].object_ref().namespace == triggering_cr.metadata.namespace.unwrap()
                        && (s.resources().contains_key(filtered_pods[i].object_ref()) ==>
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
                &&& forall |msg| {
                        let req_msg = s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.get_Some_0();
                        &&& #[trigger] s.in_flight().contains(msg)
                        &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                        &&& resp_msg_matches_req_msg(msg, req_msg)
                        &&& msg.content.is_list_response()
                    } ==> {
                        let resp_objs = msg.content.get_list_response().res.unwrap();
                        &&& msg.content.get_list_response().res.is_Ok()
                        &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 
                        &&& forall |i| #![auto] 0 <= i < resp_objs.len() ==>
                        (
                            resp_objs[i].metadata.namespace.is_some()
                            && resp_objs[i].metadata.namespace.unwrap() == triggering_cr.metadata.namespace.unwrap()
                            && (s.resources().contains_key(resp_objs[i].object_ref()) ==>
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
//
// TODO: Prove this.
//
// No hints.
//

pub open spec fn at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(
    vrs: VReplicaSetView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |diff: nat| {
            #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s)
        } ==> {
            let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
            let filtered_pods = state.filtered_pods.unwrap();
            let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
            &&& s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
            &&& VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).is_ok()
            &&& state.filtered_pods.is_Some()
            &&& diff <= filtered_pod_keys.len()
            &&& filtered_pod_keys.no_duplicates()
            &&& forall |i| #![auto] 0 <= i < diff ==> {
                &&& matching_pod_entries(vrs, s.resources()).contains_key(filtered_pod_keys[i])
                &&& matching_pod_entries(vrs, s.resources())[filtered_pod_keys[i]] == filtered_pods[i].marshal()
            }
        }
    }
}
//
// TODO: Prove this.
//
// We prove this by first showing that in the AfterListPods -> AfterDeletePod transition, that
// the `filtered_pods` variable contains matching pods in etcd. Next, we show that for
// AfterDeletePod(diff) => AfterDeletePod(diff - 1), that the pods `filtered_pods[i]`, for
// i = 1..diff - 2 are unaffected, since `filtered_pods[diff - 1]` is deleted, and the invariant 
// will hold after `diff` is decreased.
// 
// This invariant may have to be moved to a later phase, since I think this invariant will rely
// on other invariants.
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
//
// TODO: Prove this.
//
// Every delete request must be on an object with a resource version less than the resource version counter.
//

}