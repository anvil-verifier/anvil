// state-encoding predicates dedicated for liveness proofs in resource_match.rs

use crate::kubernetes_api_objects::{spec::{resource::*, prelude::*}, error::APIError::*};
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::*, message::*};
use crate::vstatefulset_controller::trusted::{spec_types::*, step::VStatefulSetReconcileStepView::*, liveness_theorem::*};
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

pub open spec fn local_state(s: ClusterState, vsts: VStatefulSetView, controller_id: int) -> VStatefulSetReconcileState {
    VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0
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
        &&& exists |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg_is_ok_list_resp_of_pods(vsts, resp_msg, s)
        }
    }
}

pub open spec fn resp_msg_is_pending_list_pod_resp_in_flight_with_n_condemned_pods(
    vsts: VStatefulSetView, controller_id: int, resp_msg: Message, condemned_len: nat
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
        let pods = objects_to_pods(resp_objs)->0;
        let filtered_pods = pods.filter(pod_filter(vsts));
        // predicate on req_msg, it's not in_flight
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_list_pod_req(vsts.object_ref(), controller_id, req_msg)
        // predicate on resp_msg
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg_is_ok_list_resp_of_pods(vsts, resp_msg, s)
        &&& partition_pods(vsts.metadata.name->0, replicas(vsts), filtered_pods).1.len() == condemned_len
    }
}

// because we have controller_owner_ref which requires uid, key alone is not enough
pub open spec fn resp_msg_is_ok_list_resp_of_pods(
    vsts: VStatefulSetView, resp_msg: Message, s: ClusterState
) -> bool {
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    // these objects can be guarded by rely conditions
    let owned_objs = resp_objs.filter(|obj: DynamicObjectView| obj.metadata.owner_references_contains(vsts.controller_owner_ref()));
    &&& resp_msg.content.is_list_response()
    &&& resp_msg.content.get_list_response().res is Ok
    &&& resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref()).no_duplicates()
    // coherence with etcd which preserves across steps taken by other controllers satisfying rely conditions
    &&& owned_objs.to_set().map(|obj: DynamicObjectView| obj.object_ref())
        == s.resources().values().filter(valid_owned_object_filter(vsts)).map(|obj: DynamicObjectView| obj.object_ref())
    &&& forall |obj: DynamicObjectView| #[trigger] owned_objs.contains(obj) ==> {
        let key = obj.object_ref();
        let etcd_obj = s.resources()[key];
        &&& s.resources().contains_key(key)
        &&& weakly_eq(obj, etcd_obj)
    }
    &&& forall |obj: DynamicObjectView| #[trigger] resp_objs.contains(obj) ==> {
        &&& obj.kind == Kind::PodKind
        &&& PodView::unmarshal(obj) is Ok
        &&& obj.metadata.name is Some
        &&& obj.metadata.namespace is Some
        &&& obj.metadata.namespace->0 == vsts.metadata.namespace->0
    }
    &&& objects_to_pods(resp_objs) is Some
}

pub open spec fn after_handle_list_pod_helper(
    vsts: VStatefulSetView, controller_id: int, condemned_len: nat, outdated_len: nat
) -> StatePred<ClusterState> {
    if replicas(vsts) > 0 {
        if pvc_cnt(vsts) > 0 {
            and!(
                at_vsts_step(vsts, controller_id, at_step![GetPVC]),
                local_state_is_valid_and_coherent(vsts, controller_id),
                no_pending_req_in_cluster(vsts, controller_id),
                pvc_needed_condemned_index_condemned_len_and_outdated_len_are(
                    vsts, controller_id, nat0!(), nat0!(), nat0!(), condemned_len, outdated_len
                )
            )
        } else {
            and!(
                at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded]),
                local_state_is_valid_and_coherent(vsts, controller_id),
                no_pending_req_in_cluster(vsts, controller_id),
                pvc_needed_condemned_index_condemned_len_and_outdated_len_are(
                    vsts, controller_id, nat0!(), nat0!(), nat0!(), condemned_len, outdated_len
                )
            )
        }
    } else {
        if condemned_len > 0 {
            and!(
                at_vsts_step(vsts, controller_id, at_step![DeleteCondemned]),
                local_state_is_valid_and_coherent(vsts, controller_id),
                no_pending_req_in_cluster(vsts, controller_id),
                pvc_needed_condemned_index_condemned_len_and_outdated_len_are(
                    vsts, controller_id, pvc_cnt(vsts), nat0!(), nat0!(), condemned_len, outdated_len
                )
            )
        } else {
            and!(
                at_vsts_step(vsts, controller_id, at_step![DeleteOutdated]),
                local_state_is_valid_and_coherent(vsts, controller_id),
                no_pending_req_in_cluster(vsts, controller_id),
                pvc_needed_condemned_index_condemned_len_and_outdated_len_are(
                    vsts, controller_id, pvc_cnt(vsts), nat0!(), nat0!(), nat0!(), outdated_len
                )
            )
        }
    }
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
    let pvc_cnt = pvc_cnt(vsts);
    &&& state.needed.len() == vsts.spec.replicas.unwrap_or(1)
    &&& state.needed_index <= state.needed.len() // they have nat type so always >= 0
    &&& state.condemned_index <= state.condemned.len()
    &&& state.pvc_index <= pvc_cnt
    &&& state.pvcs.len() == pvc_cnt
    &&& state.reconcile_step == GetPVC ==> state.pvc_index < state.pvcs.len()
    &&& forall |ord: nat| #![trigger state.needed[ord as int]] ord < state.needed.len() && state.needed[ord as int] is Some
        ==> {
            &&& state.needed[ord as int]->0.metadata.name == Some(pod_name(vsts.metadata.name->0, ord))
            &&& state.needed[ord as int]->0.metadata.namespace == Some(vsts.metadata.namespace->0)
            &&& vsts.spec.selector.matches(state.needed[ord as int]->0.metadata.labels.unwrap_or(Map::empty()))
        }
    &&& forall |i: nat| #![trigger state.condemned[i as int]] i < state.condemned.len()
        ==> {
            let condemned_pod = state.condemned[i as int];
            let condemned_pod_name = condemned_pod.metadata.name->0;
            // implies that their name will not collide with needed pods
            &&& condemned_pod.metadata.name is Some
            &&& get_ordinal(vsts.metadata.name->0, condemned_pod_name) is Some
            &&& get_ordinal(vsts.metadata.name->0, condemned_pod_name)->0 >= vsts.spec.replicas.unwrap_or(1)
            &&& condemned_pod.metadata.namespace == Some(vsts.metadata.namespace->0)
        }
    &&& forall |i: nat| #![trigger state.pvcs[i as int]] i < state.pvcs.len()
        ==> {
            &&& state.pvcs[i as int].metadata.name is Some
            &&& state.pvcs[i as int].metadata.namespace == Some(vsts.metadata.namespace->0)
            &&& state.pvcs[i as int].metadata.owner_references is None
            &&& state.pvcs[i as int].state_validation()
        }
    // pvcs have correct names
    &&& locally_at_step_or!(state, GetPVC, AfterGetPVC, CreatePVC, AfterCreatePVC, SkipPVC) ==> {
        &&& forall |i: nat| #![trigger state.pvcs[i as int]] i < pvc_cnt ==> {
            let pvc_name_expected = pvc_name(vsts.spec.volume_claim_templates->0[i as int].metadata.name->0, vsts.metadata.name->0, state.needed_index);
            state.pvcs[i as int].metadata.name == Some(pvc_name_expected)
        }
    }
    // in these states needed_index cannot be equal to needed.len()
    &&& locally_at_step_or!(state, GetPVC, AfterGetPVC, CreatePVC, AfterCreatePVC, SkipPVC, CreateNeeded, UpdateNeeded)
        ==> state.needed_index < state.needed.len()
    // because pvc index is just incremented
    &&& state.reconcile_step == AfterCreatePVC ==> state.pvc_index > 0
    // reachable condition
    &&& state.reconcile_step == CreateNeeded ==> state.needed[state.needed_index as int] is None
    &&& state.reconcile_step == AfterCreateNeeded ==> state.needed[state.needed_index - 1] is None
    &&& state.reconcile_step == UpdateNeeded ==> state.needed[state.needed_index as int] is Some
    &&& state.reconcile_step == AfterUpdateNeeded ==> state.needed[state.needed_index - 1] is Some
    &&& state.reconcile_step == DeleteCondemned ==> state.condemned_index < state.condemned.len()
    &&& state.reconcile_step == AfterDeleteCondemned ==> state.condemned_index > 0
    &&& state.reconcile_step == AfterDeleteOutdated ==> get_largest_unmatched_pods(vsts, state.needed) is Some
    &&& locally_at_step_or!(state, AfterCreateNeeded, AfterUpdateNeeded) ==> state.needed_index > 0
    // in these states pvc index is strictly less than pvc count
    &&& locally_at_step_or!(state, GetPVC, AfterGetPVC, CreatePVC, SkipPVC) ==> state.pvc_index < pvc_cnt
    // precondition to transit to CreateNeeded or UpdateNeeded
    &&& locally_at_step_or!(state, CreateNeeded, UpdateNeeded) ==> state.pvc_index == pvc_cnt
    // before reaching condemned step the index is 0
    &&& !locally_at_step_or!(state, DeleteCondemned, AfterDeleteCondemned, DeleteOutdated, AfterDeleteOutdated, Done) ==> state.condemned_index == 0
}

// coherence between local state and etcd state
// Note: there are many exceptions when the object is just updated or the index haven't been incremented yet
// message predicates for each exceptional states carry the necessary information to repair the coherence
// because of the complexity, don't forget to hide this spec when needed by
// hide(local_state_is_coherent_with_etcd);
// TODO: simplify this by removing unnecessary coherence predicates
// because controller tolerates NotFound/AlreadyExists errors
pub open spec fn local_state_is_coherent_with_etcd(vsts: VStatefulSetView, state: VStatefulSetReconcileState) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let vsts_key = vsts.object_ref();
        let pvc_cnt = if vsts.spec.volume_claim_templates is Some {
            vsts.spec.volume_claim_templates->0.len()
        } else {0};
        let needed_index_for_pvc = match state.reconcile_step {
            CreateNeeded | UpdateNeeded => (state.needed_index + 1) as nat,
            _ => state.needed_index,
        };
        let needed_index_considering_creation = match state.reconcile_step {
            AfterCreateNeeded => (state.needed_index - 1) as nat,
            _ => state.needed_index,
        };
        let condemned_index_considering_deletion = match state.reconcile_step {
            AfterDeleteCondemned => (state.condemned_index - 1) as nat,
            _ => state.condemned_index,
        };
        let outdated_pod = get_largest_unmatched_pods(vsts, state.needed);
        let outdated_pod_keys = state.needed.filter(outdated_pod_filter(vsts)).map_values(|pod_opt: Option<PodView>| pod_opt->0.object_ref());
        // 1. coherence of needed pods
        &&& forall |ord: nat| {
            &&& ord < state.needed.len()
            &&& state.needed[ord as int] is Some || ord < needed_index_considering_creation
            // at last step, one outdated pod will be deleted
            &&& !locally_at_step_or!(state, AfterDeleteOutdated, Done)
                || outdated_pod is None
                || ord != get_ordinal(vsts.metadata.name->0, outdated_pod->0.metadata.name->0)->0
        } ==> {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: #[trigger] pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            let obj = s.resources()[key];
            &&& s.resources().contains_key(key)
            &&& vsts.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
            &&& state.needed[ord as int] is Some ==> pod_weakly_eq(state.needed[ord as int]->0, PodView::unmarshal(obj)->Ok_0)
        }
        // all outdated pods are captured
        &&& outdated_pod_keys.no_duplicates()
        &&& outdated_pod is None ==> outdated_pod_keys.to_set() == outdated_obj_keys_in_etcd(s, vsts)
        &&& outdated_pod is Some ==> match state.reconcile_step {
            AfterDeleteOutdated => if s.resources().contains_key(outdated_pod->0.object_ref()) { // not deleted yet
                // this predicate is crafted in a way that even if we don't know if s.resources contains the key,
                // which is the case here because the controller tolerates NotFound error,
                outdated_pod_keys.to_set() == outdated_obj_keys_in_etcd(s, vsts)
            } else {
                // the post condition is still strong enough
                outdated_pod_keys.to_set().remove(outdated_pod->0.object_ref()) == outdated_obj_keys_in_etcd(s, vsts)
            },
            Done => outdated_pod_keys.to_set().remove(outdated_pod->0.object_ref()) == outdated_obj_keys_in_etcd(s, vsts),
            _ => outdated_pod_keys.to_set() == outdated_obj_keys_in_etcd(s, vsts),
        }
        // coherence of condemned pods
        // we have 2 ways to encode this:
        // either all pods with ord greater or equal than get_ordinal(vsts_name, state.condemned[condemned_index].metadata.name->0) are deleted
        // or use 2.a|b below, which is chosen because I don't bother to talk about order
        // 2.a. all pods to be condemned in etcd are captured in state.condemned
        &&& forall |ord: nat| ord >= vsts.spec.replicas.unwrap_or(1) ==> {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: #[trigger] pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            s.resources().contains_key(key)
                ==> exists |pod: PodView| #[trigger] state.condemned.contains(pod) && pod.object_ref() == key
        }
        // 2.b. all pods before condemned_index are deleted
        &&& forall |i: nat| #![trigger state.condemned[i as int]] i < condemned_index_considering_deletion ==> {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: state.condemned[i as int].metadata.name->0,
                namespace: vsts.metadata.namespace->0
            };
            &&& !s.resources().contains_key(key)
        }
        // 3. coherence of bound PVCs
        // all PVCs for pods before needed_index exist in etcd
        // needed_index_for_pvc is used because at CreateNeeded step the index is not yet incremented
        &&& forall |index: (nat, nat)| index.0 < needed_index_for_pvc && index.1 < pvc_cnt ==> {
            let key = ObjectRef {
                kind: PersistentVolumeClaimView::kind(),
                name: #[trigger] pvc_name(vsts.spec.volume_claim_templates->0[index.1 as int].metadata.name->0, vsts.metadata.name->0, index.0),
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
            &&& forall |i: nat| i < pvc_index_tmp ==> {
                let key = ObjectRef {
                    kind: PersistentVolumeClaimView::kind(),
                    name: #[trigger] pvc_name(vsts.spec.volume_claim_templates->0[i as int].metadata.name->0, vsts.metadata.name->0, state.needed_index),
                    namespace: vsts.metadata.namespace->0
                };
                &&& s.resources().contains_key(key)
            }
        }
    }
}

pub open spec fn pvc_needed_condemned_index_condemned_len_and_outdated_len_are(
    vsts: VStatefulSetView, controller_id: int, pvc_index: nat, needed_index: nat, condemned_index: nat, condemned_len: nat, outdated_len: nat
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        &&& local_state.pvc_index == pvc_index
        &&& local_state.needed_index == needed_index
        &&& local_state.condemned_index == condemned_index
        &&& local_state.condemned.len() == condemned_len
        &&& local_state.needed.filter(outdated_pod_filter(vsts)).len() == outdated_len
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
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let (ord, i) = (local_state.needed_index, local_state.pvc_index);
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_get_pvc_req(vsts, controller_id, req_msg, ord, i)
        &&& exists |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.is_get_response()
            &&& resp_msg.content.get_get_response().res is Err
                ==> resp_msg.content.get_get_response().res->Err_0 == ObjectNotFound
            &&& resp_msg.content.get_get_response().res is Ok
                ==> s.resources().contains_key(req_msg.content.get_get_request().key())
        }
    }
}

pub open spec fn resp_msg_is_pending_get_pvc_resp_in_flight(
    vsts: VStatefulSetView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let (ord, i) = (local_state.needed_index, local_state.pvc_index);
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_get_pvc_req(vsts, controller_id, req_msg, ord, i)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
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
    let obj = req_msg.content.get_create_request().obj;
    let key = ObjectRef {
        kind: Kind::PersistentVolumeClaimKind,
        namespace: vsts.metadata.namespace->0,
        name: pvc_name(vsts.spec.volume_claim_templates->0[i as int].metadata.name->0, vsts.metadata.name->0, ord)
    };
    let pvc = PersistentVolumeClaimView::unmarshal(obj)->Ok_0;
    &&& 0 <= i < vsts.spec.volume_claim_templates->0.len() // sanity check
    &&& req_msg.src == HostId::Controller(controller_id, vsts.object_ref())
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content is APIRequest
    &&& resource_create_request_msg(key)(req_msg)
    // to pass creation validation checks
    &&& PersistentVolumeClaimView::unmarshal(obj) is Ok
    &&& obj.metadata.namespace->0 == vsts.metadata.namespace->0
    &&& obj.metadata.owner_references is None
    &&& pvc.state_validation()
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
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let (ord, i) = (local_state.needed_index, (local_state.pvc_index - 1) as nat);
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_create_pvc_req(vsts, controller_id, req_msg, ord, i)
        // the created PVC exists in etcd
        &&& s.resources().contains_key(req_msg.content.get_create_request().key())
        &&& exists |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.is_create_response()
            &&& resp_msg.content.get_create_response().res is Err
                ==> resp_msg.content.get_create_response().res->Err_0 == ObjectAlreadyExists
        }
    }
}

pub open spec fn resp_msg_is_pending_create_pvc_resp_in_flight_and_created_pvc_exists(
    vsts: VStatefulSetView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let (ord, i) = (local_state.needed_index, (local_state.pvc_index - 1) as nat);
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_create_pvc_req(vsts, controller_id, req_msg, ord, i)
        // the created PVC exists in etcd
        &&& s.resources().contains_key(req_msg.content.get_create_request().key())
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg.content.is_create_response()
        &&& resp_msg.content.get_create_response().res is Err
            ==> resp_msg.content.get_create_response().res->Err_0 == ObjectAlreadyExists
    }
}

// NOTE: needed_index is just updated after sending the request
pub open spec fn req_msg_is_create_needed_pod_req(
    vsts: VStatefulSetView, controller_id: int, req_msg: Message, ord: nat
) -> bool {
    let req = req_msg.content.get_create_request();
    let key = ObjectRef {
        kind: Kind::PodKind,
        name: pod_name(vsts.metadata.name->0, ord),
        namespace: vsts.metadata.namespace->0
    };
    let pod = PodView::unmarshal(req.obj)->Ok_0;
    &&& req_msg.src == HostId::Controller(controller_id, vsts.object_ref())
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content is APIRequest
    &&& resource_create_request_msg(key)(req_msg)
    &&& PodView::unmarshal(req.obj) is Ok
    &&& pod_spec_matches(vsts, pod)
    // pass creation validation checks
    &&& req.obj.metadata.namespace->0 == vsts.metadata.namespace->0
    &&& pod.metadata.owner_references == Some(seq![vsts.controller_owner_ref()])
}

pub open spec fn pending_create_needed_pod_req_in_flight(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let ord = (local_state.needed_index - 1) as nat;
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_create_needed_pod_req(vsts, controller_id, req_msg, ord)
    }
}

pub open spec fn pending_create_needed_pod_resp_in_flight_and_created_pod_exists(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let resp_msg = resp_msg_or_none(s, vsts.object_ref(), controller_id)->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let ord = (local_state.needed_index - 1) as nat;
        let key = req_msg.content.get_create_request().key();
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_create_needed_pod_req(vsts, controller_id, req_msg, ord)
        // the created Pod exists in etcd
        &&& s.resources().contains_key(key)
        &&& exists |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.is_create_response()
            &&& resp_msg.content.get_create_response().res is Err
                ==> resp_msg.content.get_create_response().res->Err_0 == ObjectAlreadyExists
        }
    }
}

pub open spec fn resp_msg_is_pending_create_needed_pod_resp_in_flight_and_created_pod_exists(
    vsts: VStatefulSetView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let ord = (local_state.needed_index - 1) as nat;
        let key = req_msg.content.get_create_request().key();
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_create_needed_pod_req(vsts, controller_id, req_msg, ord)
        // the created Pod exists in etcd
        &&& s.resources().contains_key(key)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg.content.is_create_response()
        &&& resp_msg.content.get_create_response().res is Err
            ==> resp_msg.content.get_create_response().res->Err_0 == ObjectAlreadyExists
    }
}

pub open spec fn req_msg_is_get_then_update_needed_pod_req(
    vsts: VStatefulSetView, controller_id: int, req_msg: Message, ord: nat, old_pod: PodView
) -> bool {
    let req = req_msg.content.get_get_then_update_request();
    let key = ObjectRef {
        kind: Kind::PodKind,
        name: pod_name(vsts.metadata.name->0, ord),
        namespace: vsts.metadata.namespace->0
    };
    let pod = PodView::unmarshal(req.obj)->Ok_0;
    &&& req_msg.src == HostId::Controller(controller_id, vsts.object_ref())
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content is APIRequest
    &&& resource_get_then_update_request_msg(key)(req_msg)
    &&& req.owner_ref == vsts.controller_owner_ref()
    &&& PodView::unmarshal(req.obj) is Ok
    // the request does not change the uptodate status of the pod
    &&& pod_weakly_eq(pod, old_pod)
    // pod has matching labels
    &&& vsts.spec.selector.matches(req.obj.metadata.labels.unwrap_or(Map::empty()))
    // can pass update admission checks
    &&& req.obj.metadata.namespace is Some
    &&& req.obj.metadata.namespace->0 == vsts.metadata.namespace->0
    &&& req.obj.metadata.name == Some(pod_name(vsts.metadata.name->0, ord))
    &&& req.obj.metadata.owner_references == Some(seq![vsts.controller_owner_ref()])
}

pub open spec fn pending_get_then_update_needed_pod_req_in_flight(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let ord = (local_state.needed_index - 1) as nat;
        let old_pod = local_state.needed[local_state.needed_index - 1]->0;
        let key = req_msg.content.get_get_then_update_request().key();
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& s.resources().contains_key(key)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_get_then_update_needed_pod_req(vsts, controller_id, req_msg, ord, old_pod)
        &&& 0 < local_state.needed_index <= local_state.needed.len()
    }
}

pub open spec fn pending_get_then_update_needed_pod_resp_in_flight(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let ord = (local_state.needed_index - 1) as nat;
        let old_pod = local_state.needed[local_state.needed_index - 1]->0;
        let key = req_msg.content.get_get_then_update_request().key();
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& s.resources().contains_key(key)
        &&& req_msg_is_get_then_update_needed_pod_req(vsts, controller_id, req_msg, ord, old_pod)
        &&& exists |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.is_get_then_update_response()
            &&& resp_msg.content.get_get_then_update_response().res is Ok
        }
    }
}

pub open spec fn resp_msg_is_pending_get_then_update_needed_pod_resp_in_flight(
    vsts: VStatefulSetView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let ord = (local_state.needed_index - 1) as nat;
        let old_pod = local_state.needed[local_state.needed_index - 1]->0;
        let key = req_msg.content.get_get_then_update_request().key();
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& s.resources().contains_key(key)
        &&& req_msg_is_get_then_update_needed_pod_req(vsts, controller_id, req_msg, ord, old_pod)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg.content.is_get_then_update_response()
        &&& resp_msg.content.get_get_then_update_response().res is Ok
    }
}

pub open spec fn req_msg_is_get_then_delete_condemned_pod_req_carrying_condemned_pod_key(
    vsts: VStatefulSetView, controller_id: int, req_msg: Message, condemned_pod_key: ObjectRef
) -> bool {
    let req = req_msg.content.get_get_then_delete_request();
    &&& req_msg.src == HostId::Controller(controller_id, vsts.object_ref())
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content is APIRequest
    &&& resource_get_then_delete_request_msg(condemned_pod_key)(req_msg)
    &&& req.owner_ref == vsts.controller_owner_ref()
}

pub open spec fn pending_get_then_delete_condemned_pod_req_in_flight(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let condemned_pod_key = ObjectRef {
            kind: Kind::PodKind,
            name: local_state.condemned[local_state.condemned_index - 1].metadata.name->0,
            namespace: vsts.metadata.namespace->0
        };
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_get_then_delete_condemned_pod_req_carrying_condemned_pod_key(vsts, controller_id, req_msg, condemned_pod_key)
    }
}

pub open spec fn pending_get_then_delete_condemned_pod_resp_in_flight_and_condemned_pod_is_deleted(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let condemned_pod_key = ObjectRef {
            kind: Kind::PodKind,
            name: local_state.condemned[local_state.condemned_index - 1].metadata.name->0,
            namespace: vsts.metadata.namespace->0
        };
        // condemned pod is deleted from etcd
        &&& !s.resources().contains_key(condemned_pod_key)
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_get_then_delete_condemned_pod_req_carrying_condemned_pod_key(vsts, controller_id, req_msg, condemned_pod_key)
        &&& exists |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.is_get_then_delete_response()
            &&& resp_msg.content.get_get_then_delete_response().res is Err
                ==> resp_msg.content.get_get_then_delete_response().res->Err_0 == ObjectNotFound
        }
    }
}

pub open spec fn resp_msg_is_pending_get_then_delete_condemned_pod_resp_in_flight_and_condemned_pod_is_deleted(
    vsts: VStatefulSetView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let condemned_pod_key = ObjectRef {
            kind: Kind::PodKind,
            name: local_state.condemned[local_state.condemned_index - 1].metadata.name->0,
            namespace: vsts.metadata.namespace->0
        };
        // condemned pod is deleted from etcd
        &&& !s.resources().contains_key(condemned_pod_key)
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_get_then_delete_condemned_pod_req_carrying_condemned_pod_key(vsts, controller_id, req_msg, condemned_pod_key)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg.content.is_get_then_delete_response()
        &&& resp_msg.content.get_get_then_delete_response().res is Err
            ==> resp_msg.content.get_get_then_delete_response().res->Err_0 == ObjectNotFound
    }
}

pub open spec fn req_msg_is_get_then_delete_outdated_pod_req(
    vsts: VStatefulSetView, controller_id: int, req_msg: Message, outdated_pod_key: ObjectRef
) -> bool {
    &&& req_msg.src == HostId::Controller(controller_id, vsts.object_ref())
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content is APIRequest
    &&& resource_get_then_delete_request_msg(outdated_pod_key)(req_msg)
}

pub open spec fn pending_get_then_delete_outdated_pod_req_in_flight(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let outdated_pod = get_largest_unmatched_pods(vsts, local_state.needed)->0;
        let outdated_pod_key = ObjectRef {
            kind: Kind::PodKind,
            name: outdated_pod.metadata.name->0,
            namespace: vsts.metadata.namespace->0
        };
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_get_then_delete_outdated_pod_req(vsts, controller_id, req_msg, outdated_pod_key)
    }
}

pub open spec fn pending_get_then_delete_outdated_pod_resp_in_flight_and_outdated_pod_is_deleted(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let outdated_pods = local_state.needed.filter(outdated_pod_filter(vsts));
        let outdated_pod_key = ObjectRef {
            kind: Kind::PodKind,
            name: outdated_pods.last()->0.metadata.name->0,
            namespace: vsts.metadata.namespace->0
        };
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        // outdated pod is deleted from etcd
        &&& !s.resources().contains_key(outdated_pod_key)
        &&& req_msg_is_get_then_delete_outdated_pod_req(vsts, controller_id, req_msg, outdated_pod_key)
        &&& exists |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.is_get_then_delete_response()
            &&& resp_msg.content.get_get_then_delete_response().res is Err
                ==> resp_msg.content.get_get_then_delete_response().res->Err_0 == ObjectNotFound
        }
    }
}

pub open spec fn resp_msg_is_pending_get_then_delete_outdated_pod_resp_in_flight_and_outdated_pod_is_deleted(
    vsts: VStatefulSetView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
        let outdated_pods = local_state.needed.filter(outdated_pod_filter(vsts));
        let outdated_pod_key = ObjectRef {
            kind: Kind::PodKind,
            name: outdated_pods.last()->0.metadata.name->0,
            namespace: vsts.metadata.namespace->0
        };
        // outdated pod is deleted from etcd
        &&& !s.resources().contains_key(outdated_pod_key)
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_get_then_delete_outdated_pod_req(vsts, controller_id, req_msg, outdated_pod_key)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg.content.is_get_then_delete_response()
        &&& resp_msg.content.get_get_then_delete_response().res is Err
            ==> resp_msg.content.get_get_then_delete_response().res->Err_0 == ObjectNotFound
    }
}

pub open spec fn n_outdated_pods_in_etcd(vsts: VStatefulSetView, n: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        outdated_obj_keys_in_etcd(s, vsts).len() == n
    }
}

pub open spec fn reconcile_idle(vsts: VStatefulSetView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref())
    }
}

pub open spec fn reconcile_scheduled(vsts: VStatefulSetView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref())
        &&& s.scheduled_reconciles(controller_id).contains_key(vsts.object_ref())
    }
}

pub open spec fn reconcile_idle_and_not_scheduled(vsts: VStatefulSetView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref())
        &&& !s.scheduled_reconciles(controller_id).contains_key(vsts.object_ref())
    }
}

pub open spec fn after_handle_create_or_skip_pvc_helper(
    vsts: VStatefulSetView, controller_id: int, pvc_index: nat, needed_index: nat, condemned_len: nat, outdated_len: nat
) -> StatePred<ClusterState> {
    if pvc_index < pvc_cnt(vsts) {
        and!(
            at_vsts_step(vsts, controller_id, at_step![GetPVC]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            no_pending_req_in_cluster(vsts, controller_id),
            pvc_needed_condemned_index_condemned_len_and_outdated_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len, outdated_len)
        )
    } else {
        and!(
            at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            no_pending_req_in_cluster(vsts, controller_id),
            pvc_needed_condemned_index_condemned_len_and_outdated_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len, outdated_len)
        )
    }
}

pub open spec fn after_handle_after_create_or_after_update_needed_helper(
    vsts: VStatefulSetView, controller_id: int, needed_index: nat, condemned_len: nat, outdated_len: nat
) -> StatePred<ClusterState> {
    if needed_index < replicas(vsts) {
        if pvc_cnt(vsts) > 0 {
            and!(
                at_vsts_step(vsts, controller_id, at_step![GetPVC]),
                local_state_is_valid_and_coherent(vsts, controller_id),
                no_pending_req_in_cluster(vsts, controller_id),
                pvc_needed_condemned_index_condemned_len_and_outdated_len_are(vsts, controller_id, nat0!(), needed_index, nat0!(), condemned_len, outdated_len)
            )
        } else {
            and!(
                at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded]),
                local_state_is_valid_and_coherent(vsts, controller_id),
                no_pending_req_in_cluster(vsts, controller_id),
                pvc_needed_condemned_index_condemned_len_and_outdated_len_are(vsts, controller_id, nat0!(), needed_index, nat0!(), condemned_len, outdated_len)
            )
        }
    } else {
        if condemned_len > 0 {
            and!(
                at_vsts_step(vsts, controller_id, at_step![DeleteCondemned]),
                local_state_is_valid_and_coherent(vsts, controller_id),
                no_pending_req_in_cluster(vsts, controller_id),
                pvc_needed_condemned_index_condemned_len_and_outdated_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len, outdated_len)
            )
        } else {
            and!(
                at_vsts_step(vsts, controller_id, at_step![DeleteOutdated]),
                local_state_is_valid_and_coherent(vsts, controller_id),
                no_pending_req_in_cluster(vsts, controller_id),
                pvc_needed_condemned_index_condemned_len_and_outdated_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len, outdated_len)
            )
        }
    }
}

pub open spec fn inductive_current_state_matches(vsts: VStatefulSetView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& current_state_matches(vsts)(s)
        // &&& outdated_obj_keys_in_etcd(s, vsts).len() == 0
        &&& s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref()) ==> {
            let local_state =  VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
            // weaker version of local state is valid
            // so at UpdateNeeded step the request will not break current_state_matches
            &&& forall |ord: nat| #![trigger local_state.needed[ord as int]->0] ord < local_state.needed.len() ==> {
                let needed_pod = local_state.needed[ord as int]->0;
                &&& local_state.needed[ord as int] is Some
                &&& needed_pod.metadata.name == Some(#[trigger] pod_name(vsts.metadata.name->0, ord))
                &&& needed_pod.metadata.namespace == Some(vsts.metadata.namespace->0)
                &&& pod_spec_matches(vsts, needed_pod)
                &&& vsts.spec.selector.matches(needed_pod.metadata.labels.unwrap_or(Map::empty()))
            }
            &&& local_state.needed_index <= replicas(vsts)
            &&& local_state.condemned.len() == 0
            &&& !locally_at_step_or!(local_state, Init, AfterListPod) ==> local_state.needed.len() == replicas(vsts)
            &&& at_vsts_step(vsts, controller_id, at_step_or![Init, AfterListPod, GetPVC, AfterGetPVC, CreatePVC, AfterCreatePVC, SkipPVC, UpdateNeeded, AfterUpdateNeeded, DeleteOutdated, Done, Error])(s)
            &&& match local_state.reconcile_step {
                AfterListPod => {
                    let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
                    &&& s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg is Some
                    &&& req_msg_is_list_pod_req(vsts.object_ref(), controller_id, req_msg)
                    &&& forall |msg| {
                        &&& #[trigger] s.in_flight().contains(msg)
                        &&& msg.src is APIServer
                        &&& resp_msg_matches_req_msg(msg, req_msg)
                    } ==> resp_msg_is_ok_list_resp_of_pods_after_current_state_matches(vsts, msg)
                },
                AfterUpdateNeeded => {
                    let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
                    let ord = (local_state.needed_index - 1) as nat;
                    let old_pod = local_state.needed[local_state.needed_index - 1]->0;
                    &&& local_state.needed_index > 0
                    &&& s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg is Some
                    &&& req_msg_is_get_then_update_needed_pod_req_after_current_state_matches(vsts, controller_id, req_msg, ord, old_pod)
                },
                AfterGetPVC => {
                    let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
                    &&& s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg is Some
                    &&& req_msg.content.is_get_request()
                },
                AfterCreatePVC => {
                    let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
                    let req = req_msg.content.get_create_request();
                    &&& s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg is Some
                    &&& req_msg.content.is_create_request()
                    &&& req.key().kind == Kind::PersistentVolumeClaimKind
                },
                _ => {
                    s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg is None
                }
            }
        }
    }
}

// weakened version of resp_msg_is_ok_list_resp_of_pods
pub open spec fn resp_msg_is_ok_list_resp_of_pods_after_current_state_matches(
    vsts: VStatefulSetView, resp_msg: Message
) -> bool {
    let resp_objs = resp_msg.content.get_list_response().res->Ok_0;
    let pods = objects_to_pods(resp_objs)->0;
    let filtered_pods = pods.filter(pod_filter(vsts));
    let (needed, condemned) = partition_pods(vsts.metadata.name->0, replicas(vsts), filtered_pods);
    // these objects can be guarded by rely conditions
    &&& resp_msg.content.is_list_response()
    &&& resp_msg.content.get_list_response().res is Ok
    &&& resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref()).no_duplicates()
    &&& forall |obj: DynamicObjectView| #[trigger] resp_objs.contains(obj) ==> {
        &&& obj.kind == Kind::PodKind
        &&& PodView::unmarshal(obj) is Ok
        &&& obj.metadata.name is Some
        &&& obj.metadata.namespace is Some
        &&& obj.metadata.namespace->0 == vsts.metadata.namespace->0
    }
    &&& objects_to_pods(resp_objs) is Some
    // no outdated or condemned pods exist in etcd
    &&& condemned.len() == 0
    // &&& needed.filter(outdated_pod_filter(vsts)).len() == 0
    &&& forall |ord: nat| #![trigger needed[ord as int]->0] ord < needed.len() ==> {
        let needed_pod = needed[ord as int]->0;
        &&& needed[ord as int] is Some
        &&& needed_pod.metadata.name == Some(pod_name(vsts.metadata.name->0, ord))
        &&& needed_pod.metadata.namespace == Some(vsts.metadata.namespace->0)
        &&& pod_spec_matches(vsts, needed_pod)
        &&& vsts.spec.selector.matches(needed_pod.metadata.labels.unwrap_or(Map::empty()))
    }
}

pub open spec fn req_msg_is_get_then_update_needed_pod_req_after_current_state_matches(
    vsts: VStatefulSetView, controller_id: int, req_msg: Message, ord: nat, old_pod: PodView
) -> bool {
    let req = req_msg.content.get_get_then_update_request();
    let key = ObjectRef {
        kind: Kind::PodKind,
        name: pod_name(vsts.metadata.name->0, ord),
        namespace: vsts.metadata.namespace->0
    };
    let pod = PodView::unmarshal(req.obj)->Ok_0;
    &&& req_msg.src == HostId::Controller(controller_id, vsts.object_ref())
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content is APIRequest
    &&& resource_get_then_update_request_msg(key)(req_msg)
    &&& req.owner_ref == vsts.controller_owner_ref()
    &&& PodView::unmarshal(req.obj) is Ok
    // the request does not change the uptodate status of the pod
    &&& pod_weakly_eq(pod, old_pod)
    // pod has matching labels
    &&& vsts.spec.selector.matches(req.obj.metadata.labels.unwrap_or(Map::empty()))
}

}