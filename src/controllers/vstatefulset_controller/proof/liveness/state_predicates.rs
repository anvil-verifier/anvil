// state-encoding predicates dedicated for liveness proofs in resource_match.rs

use crate::kubernetes_api_objects::{spec::{resource::*, prelude::*}, error::APIError::*};
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::*, message::*};
use crate::vstatefulset_controller::trusted::{spec_types::*, step::VStatefulSetReconcileStepView::*};
use crate::vstatefulset_controller::model::{reconciler::*, install::*};
use crate::vstatefulset_controller::proof::predicate::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub open spec fn at_vsts_step(vsts: VStatefulSetView, controller_id: int, step_pred: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let triggering_cr = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].triggering_cr).unwrap();
        let local_state = s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state;
        // let replicas = vsts.spec.replicas.unwrap_or(1) as nat;
        &&& s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref())
        &&& VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].triggering_cr).is_ok()
        &&& VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).is_ok()
        &&& step_pred(local_state)
        // alternative: make them an invariant
        &&& triggering_cr.spec == vsts.spec
        &&& triggering_cr.metadata.uid == vsts.metadata.uid
        &&& triggering_cr.metadata.deletion_timestamp is None
        // optional
        &&& triggering_cr.metadata.name is Some
        &&& triggering_cr.metadata.name == vsts.metadata.name
        &&& triggering_cr.metadata.namespace is Some
        &&& triggering_cr.metadata.namespace == vsts.metadata.namespace
    }
}

pub open spec fn req_msg_or_none(s: ClusterState, vsts: VStatefulSetView, controller_id: int) -> (req_msg: Option<Message>) {
    s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg
}

pub open spec fn resp_msg_or_none(s: ClusterState, vsts: VStatefulSetView, controller_id: int) -> (resp_msg: Option<Message>) {
    if req_msg_or_none(s, vsts, controller_id) is Some && exists |resp_msg: Message| {
        &&& #[trigger] s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg_or_none(s, vsts, controller_id)->0)
    } {
        Some(choose |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg_or_none(s, vsts, controller_id)->0)
        })
    } else {
        None
    }
}

pub open spec fn no_pending_req_in_cluster(vsts: VStatefulSetView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        Cluster::no_pending_req_msg(controller_id, s, vsts.object_ref())
    }
}

pub open spec fn req_msg_is_list_pod_req(
    vsts_key: ObjectRef, controller_id: int, req_msg: Message
) -> bool {
    let req = req_msg.content->APIRequest_0;
    &&& req_msg.src == HostId::Controller(controller_id, vsts_key)
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content is APIRequest
    &&& req is ListRequest
    &&& req->ListRequest_0 == ListRequest {
        kind: Kind::PodKind,
        namespace: vsts_key.namespace,
    }
}

pub open spec fn pending_list_pod_req_in_flight(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_list_pod_req(vsts.object_ref(), controller_id, req_msg)
    }
}

pub open spec fn pending_list_pod_resp_in_flight(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        // predicate on req_msg, it's not in_flight
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_list_pod_req(vsts.object_ref(), controller_id, req_msg)
        // predicate on resp_msg
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg_is_ok_list_resp_of_pods(vsts, resp_msg, s)
        }
    }
}

// because we have controller_owner_ref which requires uid, key alone is not enough
pub open spec fn resp_msg_is_ok_list_resp_of_pods(
    vsts: VStatefulSetView, resp_msg: Message, s: ClusterState
) -> bool {
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    let pod_list = objects_to_pods(resp_objs)->0;
    &&& resp_msg.content.is_list_response()
    &&& resp_msg.content.get_list_response().res is Ok
    &&& resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref()).no_duplicates()
    // coherence with etcd which preserves across steps taken by other controllers satisfying rely conditions
    &&& resp_objs.filter(|obj: DynamicObjectView| obj.metadata.owner_references_contains(vsts.controller_owner_ref()))
        .to_set().map(|obj: DynamicObjectView| obj.object_ref())
        == s.resources().values().filter(valid_owned_object_filter(vsts)).map(|obj: DynamicObjectView| obj.object_ref())
    &&& forall |obj: DynamicObjectView| #[trigger] resp_objs.contains(obj) ==> {
        let key = obj.object_ref();
        let etcd_obj = s.resources()[key];
        &&& obj.kind == Kind::PodKind
        &&& PodView::unmarshal(obj) is Ok
        &&& obj.metadata.name is Some
        &&& obj.metadata.namespace is Some
        &&& obj.metadata.namespace->0 == vsts.metadata.namespace->0
        &&& s.resources().contains_key(key)
        &&& weakly_eq(etcd_obj, obj)
    }
    &&& objects_to_pods(resp_objs) is Some
}

pub open spec fn local_state_is_valid_and_coherent(vsts: VStatefulSetView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let vsts_key = vsts.object_ref();
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts_key].local_state)->Ok_0;
        // local state matches given state
        &&& VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts_key].local_state) is Ok
        &&& local_state_is_valid(vsts, local_state)
        &&& local_state_is_coherent_with_etcd(vsts, local_state)(s)
    }
}

pub open spec fn local_state_is_valid(vsts: VStatefulSetView, state: VStatefulSetReconcileState) -> bool {
    let pvc_cnt = if vsts.spec.volume_claim_templates is Some {
        vsts.spec.volume_claim_templates->0.len()
    } else {0};
    &&& state.needed.len() == vsts.spec.replicas.unwrap_or(1)
    &&& state.needed_index <= state.needed.len() // they have nat type so always >= 0
    &&& state.condemned_index <= state.condemned.len()
    &&& state.pvc_index <= pvc_cnt
    &&& state.pvcs.len() == pvc_cnt
    &&& state.reconcile_step == GetPVC ==> state.pvc_index < state.pvcs.len()
    &&& forall |ord: nat| #![trigger state.needed[ord as int]] ord < state.needed.len() && state.needed[ord as int] is Some
        ==> state.needed[ord as int]->0.metadata.name == Some(pod_name(vsts.metadata.name->0, ord))
    &&& forall |pod: PodView| #[trigger] state.condemned.contains(pod)
        ==> pod.metadata.name is Some
    &&& forall |i: nat| #![trigger state.pvcs[i as int]] i < state.pvcs.len()
        ==> state.pvcs[i as int].metadata.name is Some
    // pvcs have correct names
    &&& locally_at_step_or!(state, GetPVC, AfterGetPVC, CreatePVC, AfterCreatePVC, SkipPVC) ==> {
        &&& state.needed_index < state.needed.len()
        &&& forall |i: nat| #![trigger state.pvcs[i as int]] i < pvc_cnt ==> {
            let pvc_name_expected = pvc_name(vsts.spec.volume_claim_templates->0[i as int].metadata.name->0, vsts.metadata.name->0, state.needed_index);
            state.pvcs[i as int].metadata.name == Some(pvc_name_expected)
        }
    }
    // because index is just incremented
    &&& state.reconcile_step == AfterCreatePVC ==> state.pvc_index > 0
    // stricter check
    &&& locally_at_step_or!(state, GetPVC, AfterGetPVC, CreatePVC, SkipPVC) ==> state.pvc_index < pvc_cnt
}


pub open spec fn local_state_is_coherent_with_etcd(vsts: VStatefulSetView, state: VStatefulSetReconcileState) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let vsts_key = vsts.object_ref();
        let pvc_cnt = if vsts.spec.volume_claim_templates is Some {
            vsts.spec.volume_claim_templates->0.len()
        } else {0};
        // 1. coherence of needed pods
        &&& forall |ord: nat| #![trigger state.needed[ord as int]] {
            ||| ord < state.needed.len() && state.needed[ord as int] is Some
            ||| ord < state.needed_index
        } ==> {
            let key = ObjectRef {
                kind: PodView::kind(),
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            let obj = s.resources()[key];
            &&& state.needed[ord as int]->0.object_ref() == key // optional
            &&& s.resources().contains_key(key)
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
            // TODO: cover pod updates
        }
        // coherence of condemned pods
        // we have 2 ways to encode this:
        // either all pods with ord greater or equal than get_ordinal(vsts_name, state.condemned[condemned_index].metadata.name->0) are deleted
        // or use 2.a|b below, which is chosen because I don't bother to talk about order
        // 2.a. all pods to be condemned in etcd are captured in state.condemned
        &&& !exists |ord: nat| {
            let key = ObjectRef {
                kind: PodView::kind(),
                name: #[trigger] pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            let obj = s.resources()[key];
            &&& ord >= vsts.spec.replicas.unwrap_or(1)
            &&& s.resources().contains_key(key)
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
            &&& !exists |pod: PodView| #[trigger] state.condemned.contains(pod) && pod.object_ref() == key
        }
        // 2.b. all pods before condemned_index are deleted
        &&& forall |i: nat| #![trigger state.condemned[i as int]] i < state.condemned_index ==> {
            let key = state.condemned[i as int].object_ref();
            &&& !s.resources().contains_key(key)
        }
        // 3. coherence of bound PVCs
        // all PVCs for pods before needed_index exist in etcd
        &&& forall |index: (nat, nat)| #[trigger] index.0 < state.needed_index && index.1 < pvc_cnt ==> {
            let key = ObjectRef {
                kind: PersistentVolumeClaimView::kind(),
                name: pvc_name(vsts.spec.volume_claim_templates->0[index.1 as int].metadata.name->0, vsts.metadata.name->0, index.0),
                namespace: vsts.metadata.namespace->0
            };
            &&& s.resources().contains_key(key)
        }
        &&& locally_at_step_or!(state, GetPVC, AfterGetPVC, CreatePVC, AfterCreatePVC, SkipPVC) ==> {
            // PVCs for pod being processed before pvc_index exist in etcd
            // AfterCreatePVC just updates pvc_index and this only holds after APIServer creates the object
            // SkipPVC didn't increment pvc_index instantly even though that PVC exists
            let pvc_index_tmp = match state.reconcile_step {
                AfterCreatePVC => (state.pvc_index - 1) as nat,
                SkipPVC => (state.pvc_index + 1) as nat,
                _ => state.pvc_index,
            };
            &&& forall |i: nat| #![trigger vsts.spec.volume_claim_templates->0[i as int]] 
                i < pvc_index_tmp ==> {
                let key = ObjectRef {
                    kind: PersistentVolumeClaimView::kind(),
                    name: pvc_name(vsts.spec.volume_claim_templates->0[i as int].metadata.name->0, vsts.metadata.name->0, state.needed_index),
                    namespace: vsts.metadata.namespace->0
                };
                &&& s.resources().contains_key(key)
            }
        }
    }
}

pub open spec fn req_msg_is_get_pvc_req(
    vsts: VStatefulSetView, controller_id: int, req_msg: Message, ord: nat, i: nat
) -> bool {
    let req = req_msg.content->APIRequest_0;
    let key = ObjectRef {
        kind: Kind::PersistentVolumeClaimKind,
        namespace: vsts.metadata.namespace->0,
        name: pvc_name(vsts.spec.volume_claim_templates->0[i as int].metadata.name->0, vsts.metadata.name->0, ord)
    };
    &&& req_msg.src == HostId::Controller(controller_id, vsts.object_ref())
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content is APIRequest
    &&& resource_get_request_msg(key)(req_msg)
}

pub open spec fn pending_get_pvc_req_in_flight(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_get_pvc_req(vsts, controller_id, req_msg, local_state.needed_index, local_state.pvc_index)
    }
}

pub open spec fn pending_get_pvc_resp_in_flight(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let resp_msg = resp_msg_or_none(s, vsts, controller_id)->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let (ord, i) = (local_state.needed_index, local_state.pvc_index);
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_get_pvc_req(vsts, controller_id, req_msg, ord, i)
        &&& resp_msg_or_none(s, vsts, controller_id) is Some
        &&& resp_msg.content.is_get_response()
        &&& resp_msg.content.get_get_response().res is Err
            ==> resp_msg.content.get_get_response().res->Err_0 == ObjectNotFound
        &&& resp_msg.content.get_get_response().res is Ok
            ==> s.resources().contains_key(req_msg.content.get_get_request().key())
    }
}

pub open spec fn req_msg_is_create_pvc_req(
    vsts: VStatefulSetView, controller_id: int, req_msg: Message, ord: nat, i: nat
) -> bool {
    let req = req_msg.content->APIRequest_0;
    let key = ObjectRef {
        kind: Kind::PersistentVolumeClaimKind,
        namespace: vsts.metadata.namespace->0,
        name: pvc_name(vsts.spec.volume_claim_templates->0[i as int].metadata.name->0, vsts.metadata.name->0, ord)
    };
    &&& req_msg.src == HostId::Controller(controller_id, vsts.object_ref())
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content is APIRequest
    &&& resource_create_request_msg(key)(req_msg)
}

pub open spec fn pending_create_pvc_req_in_flight(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let (ord, i) = (local_state.needed_index, (local_state.pvc_index - 1) as nat);
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_create_pvc_req(vsts, controller_id, req_msg, ord, i)
    }
}

pub open spec fn pending_create_pvc_resp_msg_in_flight_and_created_pvc_exists(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let resp_msg = resp_msg_or_none(s, vsts, controller_id)->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let (ord, i) = (local_state.needed_index, (local_state.pvc_index - 1) as nat);
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_create_pvc_req(vsts, controller_id, req_msg, ord, i)
        &&& resp_msg_or_none(s, vsts, controller_id) is Some
        &&& resp_msg.content.is_create_response()
        &&& resp_msg.content.get_create_response().res is Err
            ==> resp_msg.content.get_create_response().res->Err_0 == ObjectAlreadyExists
        // the created PVC exists in etcd
        &&& s.resources().contains_key(req_msg.content.get_create_request().key())
    }
}

}