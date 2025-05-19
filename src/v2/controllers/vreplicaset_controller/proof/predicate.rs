// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
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
pub open spec fn matching_pod_keys(vrs: VReplicaSetView, resources: StoredState) -> Set<ObjectRef> {
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

pub open spec fn num_diff_pods_is(vrs: VReplicaSetView, diff: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let pods = matching_pods(vrs, s.resources());
        &&& pods.len() - vrs.spec.replicas.unwrap_or(0) == diff
    }
}

// Predicates to specify leads-to boundary lemmas.

// TODO: CONSIDER REFACTORING COMMON PARTS WITH INLINE SPEC FN.

pub open spec fn pending_req_in_flight_at_after_list_pods_step(
    vrs: VReplicaSetView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterListPods;
        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        &&& s.in_flight().contains(msg)
        &&& msg.src.is_controller_id(controller_id)
        &&& msg.dst == HostId::APIServer
        &&& msg.content.is_APIRequest()
        &&& request.is_ListRequest()
        &&& request.get_ListRequest_0() == ListRequest {
            kind: PodView::kind(),
            namespace: vrs.metadata.namespace.unwrap(),
        }
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
        &&& msg.src.is_controller_id(controller_id)
        &&& msg.dst == HostId::APIServer
        &&& msg.content.is_APIRequest()
        &&& request.is_ListRequest()
        &&& request.get_ListRequest_0() == ListRequest {
            kind: PodView::kind(),
            namespace: vrs.metadata.namespace.unwrap(),
        }
    }
}

pub open spec fn exists_resp_in_flight_at_after_list_pods_step(
    vrs: VReplicaSetView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterListPods;
        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        &&& msg.src.is_controller_id(controller_id)
        &&& msg.dst == HostId::APIServer
        &&& msg.content.is_APIRequest()
        &&& request.is_ListRequest()
        &&& request.get_ListRequest_0() == ListRequest {
            kind: PodView::kind(),
            namespace: vrs.metadata.namespace.unwrap(),
        }
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_list_response().res.is_Ok()
            &&& {
                let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                &&& matching_pods(vrs, s.resources()) == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                //&&& resp_objs.no_duplicates()
                &&& objects_to_pods(resp_objs).is_Some()
                &&& objects_to_pods(resp_objs).unwrap().no_duplicates()
                &&& resp_objs.no_duplicates()
                &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).is_Ok()
                &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
                &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
            }
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(
    vrs: VReplicaSetView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterListPods;
        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        &&& msg.src.is_controller_id(controller_id)
        &&& msg.dst == HostId::APIServer
        &&& msg.content.is_APIRequest()
        &&& request.is_ListRequest()
        &&& request.get_ListRequest_0() == ListRequest {
            kind: PodView::kind(),
            namespace: vrs.metadata.namespace.unwrap(),
        }
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_list_response().res.is_Ok()
        &&& {
            let resp_objs = resp_msg.content.get_list_response().res.unwrap();
            &&& matching_pods(vrs, s.resources()) == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
            //&&& resp_objs.no_duplicates()
            &&& objects_to_pods(resp_objs).is_Some()
            &&& objects_to_pods(resp_objs).unwrap().no_duplicates()
            &&& resp_objs.no_duplicates()
            &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).is_Ok()
            &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
            &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
        }
    }
}

// Pod creation predicates
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
        &&& msg.src.is_controller_id(controller_id)
        &&& msg.dst == HostId::APIServer
        &&& msg.content.is_APIRequest()
        &&& request.is_CreateRequest()
        &&& request.get_CreateRequest_0() == CreateRequest {
            namespace: vrs.metadata.namespace.unwrap(),
            obj: make_pod(vrs).marshal(),
        }
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
        &&& req_msg.src.is_controller_id(controller_id)
        &&& req_msg.dst == HostId::APIServer
        &&& req_msg.content.is_APIRequest()
        &&& request.is_CreateRequest()
        &&& request.get_CreateRequest_0() == CreateRequest {
            namespace: vrs.metadata.namespace.unwrap(),
            obj: make_pod(vrs).marshal(),
        }
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
        &&& msg.src.is_controller_id(controller_id)
        &&& msg.dst == HostId::APIServer
        &&& msg.content.is_APIRequest()
        &&& request.is_CreateRequest()
        &&& request.get_CreateRequest_0() == CreateRequest {
            namespace: vrs.metadata.namespace.unwrap(),
            obj: make_pod(vrs).marshal(),
        }
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
        &&& msg.src.is_controller_id(controller_id)
        &&& msg.dst == HostId::APIServer
        &&& msg.content.is_APIRequest()
        &&& request.is_CreateRequest()
        &&& request.get_CreateRequest_0() == CreateRequest {
            namespace: vrs.metadata.namespace.unwrap(),
            obj: make_pod(vrs).marshal(),
        }
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_create_response().res.is_Ok()
    }
}

// Pod deletion predicates

// The delete request must be on a matching pod.
pub open spec fn delete_constraint(
    vrs: VReplicaSetView, req: GetThenDeleteRequest
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let obj = s.resources()[req.key];
        &&& s.resources().contains_key(req.key)
        &&& matching_pods(vrs, s.resources()).contains(obj)
    }
}

pub open spec fn pending_req_in_flight_at_after_delete_pod_step(
    vrs: VReplicaSetView, controller_id: int, diff: nat
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterDeletePod(diff);
        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        let key = request.get_GetThenDeleteRequest_0().key;
        let obj = s.resources()[key];
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        &&& s.in_flight().contains(msg)
        &&& msg.src.is_controller_id(controller_id)
        &&& msg.dst == HostId::APIServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetThenDeleteRequest()
        &&& delete_constraint(vrs, request.get_GetThenDeleteRequest_0())(s)
        &&& obj.metadata.owner_references_contains(request.get_GetThenDeleteRequest_0().owner_ref)
    }
}

pub open spec fn req_msg_is_the_in_flight_delete_request_at_after_delete_pod_step(
    vrs: VReplicaSetView, controller_id: int, req_msg: Message, diff: nat
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterDeletePod(diff);
        let request = req_msg.content.get_APIRequest_0();
        let key = request.get_GetThenDeleteRequest_0().key;
        let obj = s.resources()[key];
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src.is_controller_id(controller_id)
        &&& req_msg.dst == HostId::APIServer
        &&& req_msg.content.is_APIRequest()
        &&& request.is_GetThenDeleteRequest()
        &&& delete_constraint(vrs, request.get_GetThenDeleteRequest_0())(s)
        &&& obj.metadata.owner_references_contains(request.get_GetThenDeleteRequest_0().owner_ref)
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
        &&& msg.src.is_controller_id(controller_id)
        &&& msg.dst == HostId::APIServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetThenDeleteRequest()
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_delete_response().res.is_Ok()
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
        &&& msg.src.is_controller_id(controller_id)
        &&& msg.dst == HostId::APIServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetThenDeleteRequest()
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_delete_response().res.is_Ok()
    }
}

}
