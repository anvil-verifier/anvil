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
use vstd::{prelude::*, math::abs};

verus! {

// Predicates for reasoning about model states
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

pub open spec fn no_pending_req_at_vrs_step_with_vrs(vrs: VReplicaSetView, step: VReplicaSetReconcileStep) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        &&& at_vrs_step_with_vrs(vrs, step)(s)
        &&& VRSCluster::no_pending_req_msg(s, vrs.object_ref())
    }
}

// Predicates for reasoning about pods
pub open spec fn matching_pods(vrs: VReplicaSetView, resources: StoredState) -> Set<ObjectRef> {
    Set::new(|key: ObjectRef| {
        let obj = resources[key];
        &&& resources.contains_key(key)
        &&& owned_selector_match_is(vrs, obj)
    })
}

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

pub open spec fn num_diff_pods_is(vrs: VReplicaSetView, diff: int) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        let pods = matching_pods(vrs, s.resources());
        &&& pods.len() - vrs.spec.replicas.unwrap_or(0) == diff
    }
}

// Predicates to specify leads-to boundary lemmas.
pub open spec fn pending_req_in_flight_at_after_list_pods_step(
    vrs: VReplicaSetView
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        let step = VReplicaSetReconcileStep::AfterListPods;
        let msg = s.ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, step)(s)
        &&& VRSCluster::pending_req_msg_is(s, vrs.object_ref(), msg)
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

pub open spec fn req_msg_is_the_in_flight_list_req_at_after_list_pods_step(
    vrs: VReplicaSetView, req_msg: VRSMessage
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        let step = VReplicaSetReconcileStep::AfterListPods;
        let msg = req_msg;
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, step)(s)
        &&& VRSCluster::pending_req_msg_is(s, vrs.object_ref(), msg)
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

pub open spec fn exists_resp_in_flight_at_after_list_pods_step(
    vrs: VReplicaSetView,
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        let step = VReplicaSetReconcileStep::AfterListPods;
        let msg = s.ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, step)(s)
        &&& VRSCluster::pending_req_msg_is(s, vrs.object_ref(), msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_ListRequest()
        &&& request.get_ListRequest_0() == ListRequest {
            kind: PodView::kind(),
            namespace: vrs.metadata.namespace.unwrap(),
        }
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_list_response().res.is_Ok()
            &&& {
                let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                // The matching pods must be a subset of the response.
                &&& matching_pod_entries(vrs, s.resources()).values().subset_of(resp_objs.to_set())
                &&& objects_to_pods(resp_objs).is_Some()
            }
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(
    vrs: VReplicaSetView, resp_msg: VRSMessage
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        let step = VReplicaSetReconcileStep::AfterListPods;
        let msg = s.ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, step)(s)
        &&& VRSCluster::pending_req_msg_is(s, vrs.object_ref(), msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_ListRequest()
        &&& request.get_ListRequest_0() == ListRequest {
            kind: PodView::kind(),
            namespace: vrs.metadata.namespace.unwrap(),
        }
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_list_response().res.is_Ok()
        &&& {
            let resp_objs = resp_msg.content.get_list_response().res.unwrap();
            // The matching pods must be a subset of the response.
            &&& matching_pod_entries(vrs, s.resources()).values().subset_of(resp_objs.to_set())
            &&& objects_to_pods(resp_objs).is_Some()
        }
    }
}

// Pod creation predicates
pub open spec fn pending_req_in_flight_at_after_create_pod_step(
    vrs: VReplicaSetView, diff: nat
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        let step = VReplicaSetReconcileStep::AfterCreatePod(diff as usize);
        let msg = s.ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, step)(s)
        &&& VRSCluster::pending_req_msg_is(s, vrs.object_ref(), msg)
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

pub open spec fn req_msg_is_the_in_flight_create_request_at_after_create_pod_step(
    vrs: VReplicaSetView, req_msg: VRSMessage, diff: nat
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        let step = VReplicaSetReconcileStep::AfterCreatePod(diff as usize);
        let request = req_msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, step)(s)
        &&& VRSCluster::pending_req_msg_is(s, vrs.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::CustomController
        &&& req_msg.dst == HostId::ApiServer
        &&& req_msg.content.is_APIRequest()
        &&& request.is_CreateRequest()
        &&& request.get_CreateRequest_0() == CreateRequest {
            namespace: vrs.metadata.namespace.unwrap(),
            obj: make_pod(vrs).marshal(),
        }
    }
}

pub open spec fn exists_ok_resp_in_flight_at_after_create_pod_step(
    vrs: VReplicaSetView, diff: nat
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        let step = VReplicaSetReconcileStep::AfterCreatePod(diff as usize);
        let msg = s.ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, step)(s)
        &&& VRSCluster::has_pending_k8s_api_req_msg(s, vrs.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_CreateRequest()
        &&& request.get_CreateRequest_0() == CreateRequest {
            namespace: vrs.metadata.namespace.unwrap(),
            obj: make_pod(vrs).marshal(),
        }
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_create_response().res.is_Ok()
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_create_pod_step(
    vrs: VReplicaSetView, resp_msg: VRSMessage, diff: nat
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        let step = VReplicaSetReconcileStep::AfterCreatePod(diff as usize);
        let msg = s.ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, step)(s)
        &&& VRSCluster::has_pending_k8s_api_req_msg(s, vrs.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_CreateRequest()
        &&& request.get_CreateRequest_0() == CreateRequest {
            namespace: vrs.metadata.namespace.unwrap(),
            obj: make_pod(vrs).marshal(),
        }
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_create_response().res.is_Ok()
    }
}

// Pod deletion predicates

// The delete request must be on a matching pod.
pub open spec fn delete_constraint(
    vrs: VReplicaSetView, req: DeleteRequest
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        matching_pod_entries(vrs, s.resources()).contains_key(req.key)
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
        &&& VRSCluster::pending_req_msg_is(s, vrs.object_ref(), msg)
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_DeleteRequest()
        &&& delete_constraint(vrs, request.get_DeleteRequest_0())(s)
    }
}

pub open spec fn req_msg_is_the_in_flight_delete_request_at_after_delete_pod_step(
    vrs: VReplicaSetView, req_msg: VRSMessage, diff: nat
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        let step = VReplicaSetReconcileStep::AfterDeletePod(diff as usize);
        let request = req_msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, step)(s)
        &&& VRSCluster::pending_req_msg_is(s, vrs.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::CustomController
        &&& req_msg.dst == HostId::ApiServer
        &&& req_msg.content.is_APIRequest()
        &&& request.is_DeleteRequest()
        &&& delete_constraint(vrs, request.get_DeleteRequest_0())(s)
    }
}

pub open spec fn exists_ok_resp_in_flight_at_after_delete_pod_step(
    vrs: VReplicaSetView, diff: nat
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        let step = VReplicaSetReconcileStep::AfterDeletePod(diff as usize);
        let msg = s.ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, step)(s)
        &&& VRSCluster::has_pending_k8s_api_req_msg(s, vrs.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_DeleteRequest()
        &&& delete_constraint(vrs, request.get_DeleteRequest_0())(s)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_delete_response().res.is_Ok()
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(
    vrs: VReplicaSetView, resp_msg: VRSMessage, diff: nat
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        let step = VReplicaSetReconcileStep::AfterDeletePod(diff as usize);
        let msg = s.ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, step)(s)
        &&& VRSCluster::has_pending_k8s_api_req_msg(s, vrs.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_DeleteRequest()
        &&& delete_constraint(vrs, request.get_DeleteRequest_0())(s)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_delete_response().res.is_Ok()
    }
}

}
