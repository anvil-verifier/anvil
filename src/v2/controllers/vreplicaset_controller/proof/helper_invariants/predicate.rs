// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*, 
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

// MAJOR CHANGES TO MAKE:
// Distinguish API messages coming from different sources in invariants

pub open spec fn vrs_is_well_formed(vrs: VReplicaSetView) -> StatePred<ClusterState> {
    |s: ClusterState| vrs.well_formed()
}

pub open spec fn cluster_resources_is_finite() -> StatePred<ClusterState> {
    |s: ClusterState| s.resources().dom().finite()
} 

pub open spec fn vrs_replicas_bounded(
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        0 <= vrs.spec.replicas.unwrap_or(0) <= i32::MAX // As allowed by Kubernetes.
    }
}
//
// TODO: Prove this.
//
// This should be easy to enforce with state validation.
//

pub open spec fn matching_pods_bounded(
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        0 <= matching_pod_entries(vrs, s.resources()).len() <= i32::MAX // As allowed by the previous invariant.
    }
}
//
// TODO: Prove this.
//
// This should be easy to enforce with state validation.
//

pub open spec fn vrs_selector_matches_template_labels(
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let match_value = 
            if vrs.spec.template.is_none()
            || vrs.spec.template.unwrap().metadata.is_none()
            || vrs.spec.template.unwrap().metadata.unwrap().labels.is_none() {
                Map::empty()
            } else {
                vrs.spec.template.unwrap().metadata.unwrap().labels.unwrap()
            };
        vrs.spec.selector.matches(match_value)
    }
}
//
// TODO: Prove this.
//
// This should be easy to enforce with state validation.
//

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
            &&& obj.metadata.namespace.is_Some()
            &&& content.get_create_request().namespace == obj.metadata.namespace.unwrap()
            &&& unmarshallable_object(obj, cluster.installed_types)
            &&& created_object_validity_check(created_obj, cluster.installed_types).is_none()
        }
    }
}
//
// TODO: Prove this.
//
// Proving this for the VReplicaSet controller should be easy; we'd need to do a similar
// proof for other state machines within the compound state machine.
//

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
//
// TODO: Prove this.
//
// Proving this for the VReplicaSet controller should be easy; we'd need to do a similar
// proof for other state machines within the compound state machine.
//

pub open spec fn no_pending_create_or_delete_request_not_from_controller_on_pods() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& !msg.src.is_Controller()
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        } ==> {
            &&& msg.content.is_create_request() ==> msg.content.get_create_request().key().kind != PodView::kind()
            &&& msg.content.is_delete_request() ==> msg.content.get_delete_request().key.kind != PodView::kind()
        }
    }
}
//
// TODO: Prove this.
//
// Proving this for the VReplicaSet controller should be easy; we'd need to do a similar
// proof for other state machines within the compound state machine.
//

pub open spec fn every_create_matching_pod_request_implies_at_after_create_pod_step(
    vrs: VReplicaSetView, controller_id: int,
) -> StatePred<ClusterState> {
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
            &&& owned_selector_match_is(vrs, obj)
        } ==> {
            // Need to modify these predicates.
            &&& exists |diff: usize| #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::AfterCreatePod(diff))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        }
    }
}
//
// TODO: Prove this.
//
// We know that if VReplicaSet sends a create matching pod request, that it's at an `AfterCreatePod` state.
// We show this for the other state machines by showing they don't create matching pods.
//

pub open spec fn every_delete_matching_pod_request_implies_at_after_delete_pod_step(
    vrs: VReplicaSetView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #![trigger s.in_flight().contains(msg)] {
            let content = msg.content;
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
        } ==> {
            &&& exists |diff: usize| #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::AfterDeletePod(diff))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        }
    }
}
// //
// // TODO: Prove this.
// //
// // The proof sketch for this invariant is similar to the above.
// //

// pub open spec fn each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs_if_in_etcd() -> StatePred<ClusterState> {
//     |s: ClusterState| {
//         forall |key: ObjectRef|
//             #[trigger] s.ongoing_reconciles().contains_key(key)
//             ==> {
//                 let state = s.ongoing_reconciles()[key].local_state; 
//                 let filtered_pods = state.filtered_pods.unwrap();
//                 &&& s.ongoing_reconciles()[key].triggering_cr.object_ref() == key
//                 &&& s.ongoing_reconciles()[key].triggering_cr.metadata().well_formed()
//                 &&& state.filtered_pods.is_Some()
//                 // Maintained across deletes, 
//                 // maintained across creates since all new keys with generate_name
//                 // are unique, maintained across updates since there are
//                 // no updates.
//                 &&& forall |i| #![auto] 0 <= i < filtered_pods.len() ==>
//                     (
//                         filtered_pods[i].object_ref().namespace == s.ongoing_reconciles()[key].triggering_cr.metadata.namespace.unwrap()
//                         && (s.resources().contains_key(filtered_pods[i].object_ref()) ==>
//                             s.resources()[filtered_pods[i].object_ref()].metadata.owner_references_contains(
//                                 s.ongoing_reconciles()[key].triggering_cr.controller_owner_ref()
//                             ))
//                     )
//             }
//     }
// }

pub open spec fn at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(
    vrs: VReplicaSetView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |diff: nat| {
            #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::AfterDeletePod(diff as usize))(s)
        } ==> {
            let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
            let filtered_pods = state.filtered_pods.unwrap();
            let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
            &&& s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
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

}