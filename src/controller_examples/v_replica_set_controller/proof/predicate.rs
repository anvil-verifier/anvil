// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, prelude::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::proof::controller_runtime::*;
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::defs::*;
use crate::v_replica_set_controller::model::{reconciler::*};
use crate::v_replica_set_controller::trusted::{
    liveness_theorem::*, spec_types::*, step::*,
};
use vstd::prelude::*;

verus! {

pub open spec fn at_step_closure(step: VReplicaSetReconcileStep) -> spec_fn(VReplicaSetReconcileState) -> bool {
    |s: VReplicaSetReconcileState| s.reconcile_step == step
}

pub open spec fn at_vrs_step_with_vrs(vrs: VReplicaSetView, step: VReplicaSetReconcileStep) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        &&& s.ongoing_reconciles().contains_key(vrs.object_ref())
        &&& s.ongoing_reconciles()[vrs.object_ref()].triggering_cr.object_ref() == vrs.object_ref()
        &&& s.ongoing_reconciles()[vrs.object_ref()].triggering_cr.spec() == vrs.spec()
        &&& s.ongoing_reconciles()[vrs.object_ref()].triggering_cr.metadata().uid == vrs.metadata().uid
        &&& s.ongoing_reconciles()[vrs.object_ref()].local_state.reconcile_step == step
    }
}

pub open spec fn pending_req_in_flight_at_after_list_pods_step(
    vrs: VReplicaSetView
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        let step = VReplicaSetReconcileStep::AfterListPods;
        let msg = s.ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, step)(s)
        &&& VRSCluster::has_pending_k8s_api_req_msg(s, vrs.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_ListRequest()
        &&& request.get_ListRequest_0() == ListRequest {
            kind: PodView::kind(),
            namespace: vrs.metadata.namespace.unwrap(),
        }
    }
}

pub open spec fn matching_pods(vrs: VReplicaSetView, resources: StoredState) -> Set<ObjectRef> {
    Set::new(|k: ObjectRef| owned_selector_match_is(vrs, resources, k))
}

pub open spec fn num_fewer_pods_is(vrs: VReplicaSetView, resources: StoredState, diff: nat) -> bool {
    let pods = matching_pods(vrs, resources);
    &&& pods.finite() 
    &&& (vrs.spec.replicas.unwrap_or(0) - pods.len()) as nat == diff
}

pub open spec fn num_more_pods_is(vrs: VReplicaSetView, resources: StoredState, diff: nat) -> bool {
    let pods = matching_pods(vrs, resources);
    &&& pods.finite() 
    &&& (pods.len() - vrs.spec.replicas.unwrap_or(0)) as nat == diff
}

pub open spec fn pending_req_in_flight_at_after_create_pod_step(
    vrs: VReplicaSetView, diff: nat
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        let step = VReplicaSetReconcileStep::AfterCreatePod(diff as usize);
        let msg = s.ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, step)(s)
        &&& VRSCluster::has_pending_k8s_api_req_msg(s, vrs.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_CreateRequest()
        &&& request.get_CreateRequest_0() == CreateRequest {
            namespace: vrs.metadata.namespace.unwrap(),
            obj: make_pod(vrs).marshal(),
        }
    }
}

pub open spec fn pending_req_in_flight_at_after_delete_pod_step(
    vrs: VReplicaSetView, diff: nat
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        let step = VReplicaSetReconcileStep::AfterDeletePod(diff as usize);
        let msg = s.ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, step)(s)
        &&& VRSCluster::has_pending_k8s_api_req_msg(s, vrs.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_DeleteRequest()
        // TODO: Specify this predicate further.
        // &&& request.get_CreateRequest_0() == CreateRequest {
        //     namespace: namespace,
        //     obj: make_pod(vrs).marshal(),
        // }
    }
}

}
