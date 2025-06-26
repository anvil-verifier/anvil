// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*,
    controller::types::*,
    cluster::*, 
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    proof::helper_invariants,
    trusted::{
        liveness_theorem::*,
        rely_guarantee::*,
        spec_types::*, 
        step::*
    },
};
use vstd::prelude::*;

verus! {

// General helper predicates
pub open spec fn lifted_vrs_rely_condition(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    lift_state(|s| {
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] vrs_rely(other_id)(s)
    })
}

pub open spec fn lifted_vrs_rely_condition_action(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    lift_action(|s, s_prime| {
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] vrs_rely(other_id)(s))
        && (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s_prime))
    })
}

pub open spec fn lifted_vrs_reconcile_request_only_interferes_with_itself_action(controller_id: int) -> TempPred<ClusterState> {
    lift_action(|s, s_prime| {
        (forall |vrs: VReplicaSetView| helper_invariants::vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs)(s))
        && (forall |vrs: VReplicaSetView| helper_invariants::vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs)(s_prime))
    })
}

// Predicates for reasoning about model states

pub open spec fn at_step_closure(step: VReplicaSetRecStepView) -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| VReplicaSetReconcileState::unmarshal(s).unwrap().reconcile_step == step
}

pub open spec fn unwrap_local_state_closure<T>(
    closure: spec_fn(VReplicaSetReconcileState) -> T
) -> spec_fn(ReconcileLocalState) -> T {
    |s: ReconcileLocalState| closure(VReplicaSetReconcileState::unmarshal(s).unwrap())
}

pub open spec fn at_vrs_step_with_vrs(vrs: VReplicaSetView, controller_id: int, step: VReplicaSetRecStepView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].triggering_cr).unwrap();
        let local_state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
        &&& s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
        &&& VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].triggering_cr).is_ok()
        &&& VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).is_ok()
        &&& triggering_cr.object_ref() == vrs.object_ref()
        &&& triggering_cr.spec() == vrs.spec()
        &&& triggering_cr.metadata().uid == vrs.metadata().uid
        &&& local_state.reconcile_step == step
    }
}

// Pass controller ID, unmarshal local state.
pub open spec fn no_pending_req_at_vrs_step_with_vrs(vrs: VReplicaSetView, controller_id: int, step: VReplicaSetRecStepView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::no_pending_req_msg(controller_id, s, vrs.object_ref())
    }
}

// Predicates for reasoning about pods
pub open spec fn matching_pod_entries(vrs: VReplicaSetView, resources: StoredState) -> Map<ObjectRef, DynamicObjectView> {
    Map::new(
        |key: ObjectRef| {
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& owned_selector_match_is(vrs, obj)
        },
        |key: ObjectRef| {
           resources[key]
        },
    )
}

pub open spec fn num_diff_pods_is(vrs: VReplicaSetView, diff: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let pods = matching_pods(vrs, s.resources());
        &&& pods.len() - vrs.spec.replicas.unwrap_or(0) == diff
    }
}

// Predicates to specify leads-to boundary lemmas.

pub open spec fn pending_req_in_flight_at_after_list_pods_step(
    vrs: VReplicaSetView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterListPods;
        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
        &&& req_msg_is_list_pods_req(vrs, msg)
    }
}

pub open spec fn req_msg_is_the_in_flight_list_req_at_after_list_pods_step(
    vrs: VReplicaSetView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterListPods;
        let msg = req_msg;
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
        &&& req_msg_is_list_pods_req(vrs, msg)
    }
}

pub open spec fn exists_resp_in_flight_at_after_list_pods_step(
    vrs: VReplicaSetView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterListPods;
        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
        &&& req_msg_is_list_pods_req(vrs, msg)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg_is_ok_list_resp_containing_matching_pods(s, vrs, resp_msg)
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(
    vrs: VReplicaSetView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterListPods;
        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
        &&& req_msg_is_list_pods_req(vrs, msg)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg_is_ok_list_resp_containing_matching_pods(s, vrs, resp_msg)
    }
}

pub open spec fn req_msg_is_list_pods_req(
    vrs: VReplicaSetView, req_msg: Message,
) -> bool {
    let request = req_msg.content.get_APIRequest_0();
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content.is_APIRequest()
    &&& request.is_ListRequest()
    &&& request.get_ListRequest_0() == ListRequest {
        kind: PodView::kind(),
        namespace: vrs.metadata.namespace.unwrap(),
    }
}

pub open spec fn resp_msg_is_ok_list_resp_containing_matching_pods(
    s: ClusterState, vrs: VReplicaSetView, resp_msg: Message
) -> bool {
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    let resp_obj_keys = resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref());
    &&& resp_msg.content.is_list_response()
    &&& resp_msg.content.get_list_response().res.is_Ok()
    &&& matching_pods(vrs, s.resources()) == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
    &&& objects_to_pods(resp_objs).is_Some()
    &&& objects_to_pods(resp_objs).unwrap().no_duplicates()
    &&& resp_objs.no_duplicates()
    &&& resp_obj_keys.no_duplicates()
    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).is_Ok()
    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
}

// Pod creation predicates (and function)

pub open spec fn pending_req_in_flight_at_after_create_pod_step(
    vrs: VReplicaSetView, controller_id: int, diff: nat
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterCreatePod(diff);
        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
        &&& req_msg_is_create_matching_pod_req(vrs, msg)
    }
}

pub open spec fn req_msg_is_the_in_flight_create_request_at_after_create_pod_step(
    vrs: VReplicaSetView, controller_id: int, req_msg: Message, diff: nat
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterCreatePod(diff);
        let request = req_msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::Controller(controller_id, vrs.object_ref())
        &&& req_msg_is_create_matching_pod_req(vrs, req_msg)
    }
}

pub open spec fn exists_ok_resp_in_flight_at_after_create_pod_step(
    vrs: VReplicaSetView, controller_id: int, diff: nat
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterCreatePod(diff);
        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, vrs.object_ref())
        &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
        &&& req_msg_is_create_matching_pod_req(vrs, msg)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_create_response().res.is_Ok()
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_create_pod_step(
    vrs: VReplicaSetView, controller_id: int, resp_msg: Message, diff: nat
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterCreatePod(diff);
        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, vrs.object_ref())
        &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
        &&& req_msg_is_create_matching_pod_req(vrs, msg)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_create_response().res.is_Ok()
    }
}

pub open spec fn req_msg_is_create_matching_pod_req(
    vrs: VReplicaSetView, req_msg: Message,
) -> bool {
    let request = req_msg.content.get_APIRequest_0();
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content.is_APIRequest()
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0() == CreateRequest {
        namespace: vrs.metadata.namespace.unwrap(),
        obj: make_pod(vrs).marshal(),
    }
}

pub open spec fn new_obj_in_etcd(
    s: ClusterState, cluster: Cluster, req: CreateRequest,
) -> DynamicObjectView {
    let obj_temp = req.obj;
    let meta = ObjectMetaView {
        // Set name for new object if name is not provided, here we generate
        // a unique name. The uniqueness is guaranteed by generated_name_is_unique.
        name: if obj_temp.metadata.name.is_Some() {
            obj_temp.metadata.name
        } else {
            Some(generate_name(s.api_server))
        },
        namespace: Some(req.namespace), // Set namespace for new object
        resource_version: Some(s.api_server.resource_version_counter), // Set rv for new object
        uid: Some(s.api_server.uid_counter), // Set uid for new object
        deletion_timestamp: None, // Unset deletion timestamp for new object
        ..obj_temp.metadata
    };
    DynamicObjectView {
        metadata: meta,
        status: marshalled_default_status(obj_temp.kind, cluster.installed_types), // Overwrite the status with the default one
        ..obj_temp
    }
}

// Pod deletion predicates

pub open spec fn pending_req_in_flight_at_after_delete_pod_step(
    vrs: VReplicaSetView, controller_id: int, diff: nat
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterDeletePod(diff);
        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
        &&& req_msg_is_get_then_delete_matching_pod_req(vrs, controller_id, msg)(s)
    }
}

pub open spec fn req_msg_is_the_in_flight_delete_request_at_after_delete_pod_step(
    vrs: VReplicaSetView, controller_id: int, req_msg: Message, diff: nat
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterDeletePod(diff);
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::Controller(controller_id, vrs.object_ref())
        &&& req_msg_is_get_then_delete_matching_pod_req(vrs, controller_id, req_msg)(s)
    }
}

pub open spec fn exists_ok_resp_in_flight_at_after_delete_pod_step(
    vrs: VReplicaSetView, controller_id: int, diff: nat
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterDeletePod(diff);
        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, vrs.object_ref())
        &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
        &&& msg.dst == HostId::APIServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetThenDeleteRequest()
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_get_then_delete_response().res.is_Ok()
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(
    vrs: VReplicaSetView, controller_id: int, resp_msg: Message, diff: nat
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterDeletePod(diff);
        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, vrs.object_ref())
        &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
        &&& msg.dst == HostId::APIServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetThenDeleteRequest()
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_get_then_delete_response().res.is_Ok()
    }
}

pub open spec fn req_msg_is_get_then_delete_matching_pod_req(
    vrs: VReplicaSetView, controller_id: int, req_msg: Message,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let request = req_msg.content.get_APIRequest_0();
        let key = request.get_GetThenDeleteRequest_0().key;
        let obj = s.resources()[key];
        let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
        let filtered_pods = state.filtered_pods.unwrap();
        let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
        let diff = state.reconcile_step.get_AfterDeletePod_0();
        // Basic requirements.
        &&& req_msg.dst == HostId::APIServer
        &&& req_msg.content.is_APIRequest()
        &&& request.is_GetThenDeleteRequest()
        // We require the key we are deleting is a pod in etcd owned by vrs.
        &&& s.resources().contains_key(key)
        &&& matching_pods(vrs, s.resources()).contains(obj)
        // We further require that the attached owner reference is the vrs 
        // controller owner reference.
        &&& request.get_GetThenDeleteRequest_0().owner_ref
            == vrs.controller_owner_ref()
        // We further require that the key of the sent request is the last index of
        // filtered_pods.
        &&& key == filtered_pod_keys[diff as int]
    }
}

pub open spec fn filtered_pods_in_vrs_matching_pods(
    vrs: VReplicaSetView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
        let filtered_pods = state.filtered_pods.unwrap();
        let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
        let diff = state.reconcile_step.get_AfterDeletePod_0();
        &&& s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
        &&& VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).is_ok()
        &&& state.reconcile_step.is_AfterDeletePod()
        &&& state.filtered_pods.is_Some()
        &&& filtered_pod_keys.no_duplicates()
        &&& diff < filtered_pods.len()
        &&& forall |i| #![trigger state.filtered_pods.unwrap()[i]] 0 <= i < diff ==> {
            &&& s.resources().contains_key(filtered_pod_keys[i])
            &&& matching_pods(vrs, s.resources()).contains(s.resources()[filtered_pod_keys[i]])
            &&& PodView::unmarshal(s.resources()[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
        }
    }
}

}
