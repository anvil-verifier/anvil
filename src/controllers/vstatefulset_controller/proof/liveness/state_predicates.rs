// state-encoding predicates dedicated for liveness proofs in resource_match.rs

use crate::kubernetes_api_objects::spec::{resource::*, prelude::*};
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

pub open spec fn no_pending_req_in_cluster(vsts: VStatefulSetView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        Cluster::no_pending_req_msg(controller_id, s, vsts.object_ref())
    }
}

pub open spec fn req_msg_is_list_pod_req(
    vsts_key: ObjectRef, controller_id: int, req_msg: Message, s: ClusterState
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

pub open spec fn pending_list_req_in_flight(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_list_pod_req(vsts.object_ref(), controller_id, req_msg, s)
    }
}

pub open spec fn req_msg_is_pending_list_req_in_flight(
    vsts: VStatefulSetView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_list_pod_req(vsts.object_ref(), controller_id, req_msg, s)
    }
}

pub open spec fn exists_pending_list_resp_in_flight_and_match_req(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        // predicate on req_msg, it's not in_flight
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_list_pod_req(vsts.object_ref(), controller_id, req_msg, s)
        // predicate on resp_msg
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg_is_ok_list_resp_of_pods(vsts, resp_msg, s)
        }
    }
}

pub open spec fn resp_msg_is_pending_list_resp_in_flight_and_match_req(
    vsts: VStatefulSetView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        // predicate on req_msg, it's not in_flight
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_list_pod_req(vsts.object_ref(), controller_id, req_msg, s)
        // predicate on resp_msg
        &&& #[trigger] s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg_is_ok_list_resp_of_pods(vsts, resp_msg, s)
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
    &&& resp_objs.filter(has_vsts_controller_owner_filter(vsts)).to_set().map(|obj: DynamicObjectView| obj.object_ref())
        == s.resources().values().filter(|obj: DynamicObjectView| {
            &&& obj.kind == Kind::PodKind
            &&& obj.metadata.name is Some
            &&& obj.metadata.namespace is Some
            &&& obj.metadata.owner_references is Some
            &&& obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vsts.controller_owner_ref()]
        }).map(|obj: DynamicObjectView| obj.object_ref())
    &&& resp_objs.all(|obj: DynamicObjectView| {
        let key = obj.object_ref();
        let etcd_obj = s.resources()[key];
        &&& obj.kind == Kind::PodKind
        &&& obj.metadata.name is Some
        &&& obj.metadata.namespace is Some
        &&& obj.metadata.owner_references is Some
        &&& obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vsts.controller_owner_ref()]
        &&& s.resources().contains_key(key)
        &&& weakly_eq(etcd_obj, obj)
    })
    &&& objects_to_pods(resp_objs) is Some
}

pub open spec fn local_state_is(vsts: VStatefulSetView, controller_id: int, state: VStatefulSetReconcileState) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let vsts_key = vsts.object_ref();
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts_key].local_state)->Ok_0;
        // local state matches given state
        &&& VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts_key].local_state) is Ok
        &&& local_state == state
        // validity of local state
        &&& state.needed.len() == vsts.spec.replicas.unwrap_or(1)
        &&& state.needed_index <= state.needed.len() // they have nat type so always >= 0
        &&& state.condemned_index <= state.condemned.len()
        &&& state.pvc_index <= state.pvcs.len()
        &&& forall |ord: nat| #![trigger state.needed[ord as int]] ord < state.needed.len() && state.needed[ord as int] is Some
            ==> state.needed[ord as int]->0.metadata.name == Some(pod_name(vsts.metadata.name->0, ord))
        &&& forall |i: nat| #![trigger state.condemned[i as int]] i < state.condemned.len()
            ==> state.condemned[i as int].metadata.name is Some
        &&& local_state_is_coherent_with_etcd(vsts, state)(s)
    }
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
            &&& s.resources().contains_key(key)
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
            // TODO: cover pod updates
        }
        // coherence of condemned pods
        // we have 2 ways to encode this:
        // either all pods with ord greater or equal than get_ordinal(vsts_name, state.condemned[condemned_index]) are deleted
        // or use 2.a|b below, which is chosen because I don't bother to talk about order
        // 2.a. all pods to be condemned in etcd are captured in state.condemned
        &&& forall |ord: nat| #![trigger state.condemned[ord as int]] ord >= vsts.spec.replicas.unwrap_or(1) ==> {
            let key = ObjectRef {
                kind: PodView::kind(),
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            &&& s.resources().contains_key(key) ==> {
                exists |i: nat| #![trigger state.condemned[i as int]] i < state.condemned.len() && state.condemned[i as int].metadata.name->0 == key.name
            }
        }
        // 2.b. all pods before condemned_index are deleted
        &&& forall |i: nat| #![trigger state.condemned[i as int]] i < state.condemned_index ==> {
            let key = state.condemned[i as int].object_ref();
            &&& !s.resources().contains_key(key)
        }
        // 3. coherence of bound PVCs
        &&& forall |ord: nat| #![trigger state.needed[ord as int]] ord < state.needed_index
            ==> forall |i: nat| #![trigger vsts.spec.volume_claim_templates->0[i as int]] i < pvc_cnt ==> {
                let key = ObjectRef {
                    kind: PersistentVolumeClaimView::kind(),
                    name: pvc_name(vsts.spec.volume_claim_templates->0[i as int].metadata.name->0, vsts.metadata.name->0, ord),
                    namespace: vsts.metadata.namespace->0
                };
                &&& s.resources().contains_key(key)
            }
        &&& state.reconcile_step == GetPVC || state.reconcile_step == AfterGetPVC || state.reconcile_step == AfterCreatePVC || state.reconcile_step == SkipPVC ==> {
            &&& state.needed_index < state.needed.len()
            &&& forall |i: nat| #![trigger state.pvcs[i as int]] i < state.pvc_index ==> {
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

}