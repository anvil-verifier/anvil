use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::vdeployment_controller::{
    trusted::{rely_guarantee::*, step::*, spec_types::*},
    model::{install::*, reconciler::*},
    proof::*,
};
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*
};
use crate::vdeployment_controller::{
    trusted::{step::*, spec_types::*, util::*,
        rely_guarantee::vd_rely, liveness_theorem::*},
    model::{install::*, reconciler::*},
};
use crate::vreplicaset_controller::trusted::spec_types::VReplicaSetView;
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use vstd::prelude::*;

verus! {

// predicates used for liveness reasoning
pub open spec fn at_vd_step_with_vd(vd: VDeploymentView, controller_id: int, step_pred: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
        let local_state = s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state;
        &&& s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
        &&& VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).is_ok()
        &&& VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).is_ok()
        &&& triggering_cr.object_ref() == vd.object_ref()
        &&& triggering_cr.spec() == vd.spec()
        &&& triggering_cr.metadata() == vd.metadata()
        // &&& triggering_cr.metadata().uid == vd.metadata().uid
        // &&& triggering_cr.metadata().namespace == vd.metadata().namespace
        // &&& triggering_cr.metadata().name == vd.metadata().name
        // &&& triggering_cr.metadata().labels == vd.metadata().labels
        // &&& triggering_cr.metadata().resource_version == vd.metadata().resource_version
        &&& triggering_cr.controller_owner_ref() == vd.controller_owner_ref()
        &&& triggering_cr.well_formed() == vd.well_formed()
        &&& step_pred(local_state)
    }
}

// ---- message predicates ----
// we have 2 versions of each predicate because we need to instantiate msg for wf lemmas
// and another exists |msg| is also required as post condition

pub open spec fn no_pending_req_in_cluster(vd: VDeploymentView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        Cluster::no_pending_req_msg(controller_id, s, vd.object_ref())
    }
}

pub open spec fn req_msg_is_list_vrs_req(vd: VDeploymentView, controller_id: int, req_msg: Message) -> bool {
    let request = req_msg.content.get_APIRequest_0();
    &&& req_msg.src == HostId::Controller(controller_id, vd.object_ref())
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content.is_APIRequest()
    &&& request.is_ListRequest()
    &&& request.get_ListRequest_0() == ListRequest {
        kind: VReplicaSetView::kind(),
        namespace: vd.metadata.namespace.unwrap(),
    }
}

pub open spec fn pending_list_req_in_flight(vd: VDeploymentView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_list_vrs_req(vd, controller_id, req_msg)
    }
}

pub open spec fn req_msg_is_pending_list_req_in_flight(vd: VDeploymentView, controller_id: int, req_msg: Message,) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_list_vrs_req(vd, controller_id, req_msg)
    }
}

// should be used with VReplicaSetView::marshal_preserves_integrity()
// resp is list resp matching req && resp content match etcd
pub open spec fn exists_pending_list_resp_in_flight_and_match_req(vd: VDeploymentView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        // predicate on req_msg, it's not in_flight
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_list_vrs_req(vd, controller_id, req_msg)
        // predicate on resp_msg
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg_is_ok_list_resp_containing_matched_vrs(s, vd, resp_msg)
        }
    }
}

pub open spec fn resp_msg_is_pending_list_resp_in_flight_and_match_req(
    vd: VDeploymentView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        // predicate on req_msg, it's not in_flight
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_list_vrs_req(vd, controller_id, req_msg)
        // predicate on resp_msg
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg_is_ok_list_resp_containing_matched_vrs(s, vd, resp_msg)
    }
}

/* Notes about objects(vrs) ownership:
the current version of valid_owned_object is confusing, and it couples the exec and proof parts, we should separate them when needed
Ideally, we only need the namespace to match and vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
    and the equality with vrs.metadata.owner_references_contains(vd.controller_owner_ref()) can be proved using each_object_in_etcd_has_at_most_one_controller_owner
The unmarshallability part can be proved using each_custom_object_in_etcd_is_well_formed
*/

pub open spec fn resp_msg_is_ok_list_resp_containing_matched_vrs(
    s: ClusterState, vd: VDeploymentView, resp_msg: Message
) -> bool {
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    let vrs_list = objects_to_vrs_list(resp_objs).unwrap();
    let obj_owned_by_vd = |obj: DynamicObjectView| {
        &&& obj.kind == VReplicaSetView::kind()
        &&& obj.metadata.namespace == vd.metadata.namespace
        &&& obj.metadata.owner_references is Some
        &&& obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
    };
    &&& resp_msg.content.is_list_response()
    &&& resp_msg.content.get_list_response().res is Ok
    &&& objects_to_vrs_list(resp_objs) is Some
    &&& resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref()).no_duplicates()
    &&& filter_old_and_new_vrs(vd, vrs_list.filter(|vrs| valid_owned_object(vrs, vd))) == filter_old_and_new_vrs_on_etcd(vd, s.resources())
    &&& forall |obj| #[trigger] resp_objs.contains(obj) ==> {
        &&& VReplicaSetView::unmarshal(obj) is Ok
        &&& obj_owned_by_vd(obj)
        &&& s.resources().contains_key(obj.object_ref())
        &&& s.resources()[obj.object_ref()] == obj
    }
}

pub open spec fn req_msg_is_create_vrs_req(
    vd: VDeploymentView, controller_id: int, req_msg: Message
) -> bool {
    let request = req_msg.content.get_APIRequest_0().get_CreateRequest_0();
    &&& req_msg.src == HostId::Controller(controller_id, vd.object_ref())
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content.is_APIRequest()
    &&& req_msg.content.get_APIRequest_0().is_CreateRequest()
    &&& request == CreateRequest {
        namespace: vd.metadata.namespace.unwrap(),
        obj: make_replica_set(vd).marshal()
    }
}

pub open spec fn pending_create_new_vrs_req_in_flight(
    vd: VDeploymentView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_create_vrs_req(vd, controller_id, req_msg)
    }
}

pub open spec fn req_msg_is_pending_create_new_vrs_req_in_flight(
    vd: VDeploymentView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_create_vrs_req(vd, controller_id, req_msg)
    }
}

pub open spec fn resp_msg_is_ok_create_new_vrs_resp(
    vd: VDeploymentView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_create_vrs_req(vd, controller_id, req_msg)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg.content.is_create_response()
        &&& resp_msg.content.get_create_response().res is Ok
    }
}

pub open spec fn exists_resp_msg_is_ok_create_new_vrs_resp(
    vd: VDeploymentView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_create_vrs_req(vd, controller_id, req_msg)
        &&& exists |resp_msg| {
            // predicate on resp_msg
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            // we don't need info on content of the response at the moment
            &&& resp_msg.content.is_create_response()
            &&& resp_msg.content.get_create_response().res is Ok
        }
    }
}

pub open spec fn req_msg_is_scale_down_old_vrs_req(
    vd: VDeploymentView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let request = req_msg.content.get_APIRequest_0().get_GetThenUpdateRequest_0();
        let key = request.key();
        let obj = s.resources()[key];
        let etcd_vrs = VReplicaSetView::unmarshal(obj)->Ok_0;
        let req_vrs = VReplicaSetView::unmarshal(request.obj)->Ok_0;
        let state = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        &&& req_msg.src == HostId::Controller(controller_id, vd.object_ref())
        &&& req_msg.dst == HostId::APIServer
        &&& req_msg.content.is_APIRequest()
        &&& req_msg.content.get_APIRequest_0().is_GetThenUpdateRequest()
        &&& request.namespace == vd.metadata.namespace->0
        &&& request.owner_ref == vd.controller_owner_ref()
        // stronger than local_state_is_valid_and_coherent
        &&& state.old_vrs_index < state.old_vrs_list.len()
        &&& s.resources().contains_key(key)
        // the scaled down vrs can previously pass old vrs filter
        &&& filter_old_and_new_vrs_on_etcd(vd, s.resources()).1.contains(VReplicaSetView::unmarshal(obj)->Ok_0)
        &&& valid_owned_object(req_vrs, vd)
        // etcd obj is owned by vd and should be protected by non-interference property
        &&& VReplicaSetView::unmarshal(obj) is Ok
        // unwrapped weaker version of vrs_eq_for_vd without spec as it's updated here
        &&& etcd_vrs.metadata.namespace == req_vrs.metadata.namespace
        &&& etcd_vrs.metadata.name == req_vrs.metadata.name
        &&& etcd_vrs.metadata.labels == req_vrs.metadata.labels
        &&& etcd_vrs.metadata.owner_references == req_vrs.metadata.owner_references
        // owned by vd
        &&& req_vrs.metadata.owner_references is Some
        &&& req_vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
        // scaled down vrs should not pass old vrs filter in s_prime
        &&& req_vrs.spec.replicas == Some(int0!())
        &&& key == state.old_vrs_list[state.old_vrs_index as int].object_ref()
        &&& key == req_vrs.object_ref()
    }
}

pub open spec fn req_msg_is_scale_new_vrs_req(
    vd: VDeploymentView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let request = req_msg.content.get_APIRequest_0().get_GetThenUpdateRequest_0();
        let key = request.key();
        let obj = s.resources()[key];
        let etcd_vrs = VReplicaSetView::unmarshal(obj)->Ok_0;
        let req_vrs = VReplicaSetView::unmarshal(request.obj)->Ok_0;
        let state = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        &&& req_msg.src == HostId::Controller(controller_id, vd.object_ref())
        &&& req_msg.dst == HostId::APIServer
        &&& req_msg.content.is_APIRequest()
        &&& req_msg.content.get_APIRequest_0().is_GetThenUpdateRequest()
        &&& request.namespace == vd.metadata.namespace->0
        &&& request.owner_ref == vd.controller_owner_ref()
        &&& s.resources().contains_key(key)
        // the scaled down vrs can previously pass new vrs filter
        &&& filter_old_and_new_vrs_on_etcd(vd, s.resources()).0 == Some(VReplicaSetView::unmarshal(obj)->Ok_0)
        &&& valid_owned_object(req_vrs, vd)
        // etcd obj is owned by vd and should be protected by non-interference property
        &&& VReplicaSetView::unmarshal(obj) is Ok
        // unwrapped weaker version of vrs_eq_for_vd without spec as it's updated here
        &&& etcd_vrs.metadata.namespace == req_vrs.metadata.namespace
        &&& etcd_vrs.metadata.name == req_vrs.metadata.name
        &&& etcd_vrs.metadata.labels == req_vrs.metadata.labels
        &&& etcd_vrs.metadata.owner_references == req_vrs.metadata.owner_references
        // owned by vd
        &&& req_vrs.metadata.owner_references is Some
        &&& req_vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
        // scaled down vrs should not pass old vrs filter in s_prime
        &&& req_vrs.spec.replicas == Some(vd.spec.replicas.unwrap_or(1))
        &&& key == state.new_vrs->0.object_ref()
        &&& key == req_vrs.object_ref()
    }
}

pub open spec fn req_msg_is_pending_get_then_update_old_vrs_req_in_flight(
    vd: VDeploymentView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_scale_down_old_vrs_req(vd, controller_id, req_msg)(s)
    }
}

pub open spec fn req_msg_is_pending_get_then_update_new_vrs_req_in_flight(
    vd: VDeploymentView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_scale_new_vrs_req(vd, controller_id, req_msg)(s)
    }
}

pub open spec fn pending_get_then_update_old_vrs_req_in_flight(
    vd: VDeploymentView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_scale_down_old_vrs_req(vd, controller_id, req_msg)(s)
    }
}

pub open spec fn pending_get_then_update_new_vrs_req_in_flight(
    vd: VDeploymentView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_scale_new_vrs_req(vd, controller_id, req_msg)(s)
    }
}

// currently controller does not distinguish between old vrs and new vrs response
// just need it to return ok
pub open spec fn resp_msg_is_ok_get_then_update_resp(
    vd: VDeploymentView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        let request = req_msg.content.get_APIRequest_0();
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, vd.object_ref())
        &&& req_msg.src == HostId::Controller(controller_id, vd.object_ref())
        &&& req_msg.dst == HostId::APIServer
        &&& req_msg.content.is_APIRequest()
        &&& request.is_GetThenUpdateRequest()
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg.content.get_get_then_update_response().res is Ok
    }
}

pub open spec fn exists_resp_msg_is_ok_get_then_update_resp(
    vd: VDeploymentView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        let request = req_msg.content.get_APIRequest_0();
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, vd.object_ref())
        &&& req_msg.src == HostId::Controller(controller_id, vd.object_ref())
        &&& req_msg.dst == HostId::APIServer
        &&& req_msg.content.is_APIRequest()
        &&& request.is_GetThenUpdateRequest()
        &&& exists |resp_msg| {
            // predicate on resp_msg
            &&& #[trigger] s.in_flight().contains(resp_msg)
            // we don't need info on content of the response at the moment
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_then_update_response().res is Ok
        }
    }
}

// a weaker version of coherence between local cache and etcd
// - only need the key to be in etcd and corresponding objects can pass the filter
// - so current_state_matches canexists_resp_msg_is_ok_get_then_update_resp be reached by sending get-then-update request
// this predicate holds since AfterListVRS state
pub open spec fn local_state_is_valid_and_coherent(vd: VDeploymentView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let vds = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        &&& 0 <= vds.old_vrs_index <= vds.old_vrs_list.len()
        // pending_get_then_update_old_vrs_req_in_flight ==> etcd is not yet updated
        &&& forall |i| #![trigger vds.old_vrs_list[i]] 0 <= i < vds.old_vrs_index ==> {
            let vrs = vds.old_vrs_list[i];
            let key = vrs.object_ref();
            // the get-then-update request can succeed
            &&& s.resources().contains_key(key)
            // obj in etcd exists and is owned by vd
            &&& valid_owned_object(vrs, vd)
            &&& vrs.metadata.owner_references is Some
            &&& vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
            &&& filter_old_and_new_vrs_on_etcd(vd, s.resources()).1.contains(vrs)
            &&& VReplicaSetView::unmarshal(s.resources()[key]) is Ok
            // This is too strong, we only care about metadata.{name, namespace, labels} and spec,
            // TODO: support status change
            &&& VReplicaSetView::unmarshal(s.resources()[key])->Ok_0 == vrs
        }
        // vds.old_vrs_list.no_duplicates() can be inferred by
        &&& vds.old_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref()).no_duplicates()
        // new vrs
        &&& vds.new_vrs is None ==> filter_old_and_new_vrs_on_etcd(vd, s.resources()).0 is None
        &&& vds.new_vrs is Some ==> {
            let new_vrs = vds.new_vrs->0;
            // obj in etcd exists and is owned by vd
            &&& valid_owned_object(new_vrs, vd)
            // owner_references_contains is too weak
            // TODO: investigate why this is not required for old vrs
            &&& new_vrs.metadata.owner_references is Some
            &&& new_vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
            // if it's just created, etcd should not have it yet
            // otherwise obj in etcd exists and is owned by vd
            &&& !pending_create_new_vrs_req_in_flight(vd, controller_id)(s) ==> {
                let etcd_vrs = VReplicaSetView::unmarshal(s.resources()[new_vrs.object_ref()])->Ok_0;
                // the get-then-update request can succeed
                &&& s.resources().contains_key(new_vrs.object_ref())
                &&& VReplicaSetView::unmarshal(s.resources()[new_vrs.object_ref()]) is Ok
                &&& filter_old_and_new_vrs_on_etcd(vd, s.resources()).0 is Some
                &&& (filter_old_and_new_vrs_on_etcd(vd, s.resources()).0)->0 == etcd_vrs
                // spec is not equal as the update request is in flight 
                &&& !pending_get_then_update_new_vrs_req_in_flight(vd, controller_id)(s) ==> vrs_eq_for_vd(new_vrs, etcd_vrs)
                &&& pending_get_then_update_new_vrs_req_in_flight(vd, controller_id)(s) ==> {
                    &&& etcd_vrs.metadata.namespace == new_vrs.metadata.namespace
                    &&& etcd_vrs.metadata.name == new_vrs.metadata.name
                    &&& etcd_vrs.metadata.labels == new_vrs.metadata.labels
                    &&& etcd_vrs.metadata.owner_references == new_vrs.metadata.owner_references
                }
            }
        }
    }
}

// weaker version of == for vrs excluding resource version, uid and status
pub open spec fn vrs_eq_for_vd(lhs: VReplicaSetView, rhs: VReplicaSetView) -> bool {
    &&& lhs.metadata.namespace == rhs.metadata.namespace
    &&& lhs.metadata.name == rhs.metadata.name
    &&& lhs.metadata.labels == rhs.metadata.labels
    &&& lhs.metadata.owner_references == rhs.metadata.owner_references
    &&& lhs.spec == rhs.spec
}

pub open spec fn controller_owner_filter() -> spec_fn(OwnerReferenceView) -> bool {
    |o: OwnerReferenceView| o.controller is Some && o.controller->0
}

// new_vrs_replicas is Some(x) -> new vrs exists and has replicas = x; else new vrs does not exist
pub open spec fn etcd_state_is(vd: VDeploymentView, controller_id: int, new_vrs_replicas: Option<int>, old_vrs_list_len: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let (new_vrs, old_vrs_list) = filter_old_and_new_vrs_on_etcd(vd, s.resources());
        &&& old_vrs_list.len() == old_vrs_list_len
        &&& match new_vrs_replicas {
            Some(n) => {
                &&& new_vrs is Some
                &&& new_vrs->0.spec.replicas.unwrap_or(1) == n
                &&& match_template_without_hash(vd, new_vrs->0)
            },
            None => {
                new_vrs is None
            }
        }
    }
}

pub open spec fn local_state_is(new_vrs_replicas: Option<int>, old_vrs_list_len: nat) -> spec_fn(VDeploymentReconcileState) -> bool {
    |vds: VDeploymentReconcileState| {
        &&& match new_vrs_replicas {
            Some(n) => {
                &&& vds.new_vrs is Some
                &&& vds.new_vrs->0.spec.replicas.unwrap_or(1) == n
            }
            None => vds.new_vrs is None
        }
        &&& vds.old_vrs_index == old_vrs_list_len
    }
}

pub open spec fn old_vrs_list_len(n: nat) -> spec_fn(VDeploymentReconcileState) -> bool {
    |vds: VDeploymentReconcileState| vds.old_vrs_index == n
}

pub open spec fn vd_rely_condition(vd: VDeploymentView, cluster: Cluster, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| forall |other_id| other_id != controller_id && cluster.controller_models.contains_key(other_id)
                                        ==> #[trigger] vd_rely(other_id)(s)
}

// same as vrs, similar to rely condition. Yet we talk about owner_ref here
pub open spec fn garbage_collector_does_not_delete_vd_pods(vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src.is_BuiltinController()
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        } ==> {
            let req_msg = msg.content.get_delete_request(); 
            &&& msg.content.is_delete_request()
            &&& req_msg.preconditions is Some
            &&& req_msg.preconditions.unwrap().uid is Some
            &&& req_msg.preconditions.unwrap().uid.unwrap() < s.api_server.uid_counter
            &&& s.resources().contains_key(req_msg.key) ==> {
                let etcd_obj = s.resources()[req_msg.key];
                let owner_references = etcd_obj.metadata.owner_references->0;
                ||| (!(etcd_obj.metadata.owner_references is Some) && owner_references.contains(vd.controller_owner_ref()))
                ||| etcd_obj.metadata.uid.unwrap() > req_msg.preconditions.unwrap().uid.unwrap()
            }
        }
    }
}

pub open spec fn cluster_invariants_since_reconciliation(cluster: Cluster, vd: VDeploymentView, controller_id: int) -> StatePred<ClusterState> {
    and!(
        Cluster::crash_disabled(controller_id),
        Cluster::req_drop_disabled(),
        Cluster::pod_monkey_disabled(),
        Cluster::every_in_flight_msg_has_unique_id(),
        Cluster::every_in_flight_msg_has_lower_id_than_allocator(),
        Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id),
        Cluster::each_object_in_etcd_is_weakly_well_formed(),
        cluster.each_builtin_object_in_etcd_is_well_formed(),
        cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>(),
        cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>(),
        Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id(),
        Cluster::each_object_in_etcd_has_at_most_one_controller_owner(),
        Cluster::cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(controller_id),
        Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id),
        Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id),
        Cluster::ongoing_reconciles_is_finite(controller_id),
        Cluster::cr_objects_in_reconcile_have_correct_kind::<VDeploymentView>(controller_id),
        Cluster::etcd_is_finite(),
        Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref()),
        Cluster::there_is_the_controller_state(controller_id),
        Cluster::there_is_no_request_msg_to_external_from_controller(controller_id),
        Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id),
        Cluster::desired_state_is(vd),
        Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vd.object_ref()),
        helper_invariants::no_other_pending_request_interferes_with_vd_reconcile(vd, controller_id),
        // we use lifted version for vd_reconcile_request_only_interferes_with_itself with quantifiers
        helper_invariants::garbage_collector_does_not_delete_vd_vrs_objects(vd),
        helper_invariants::every_msg_from_vd_controller_carries_vd_key(controller_id),
        helper_invariants::vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id),
        helper_invariants::no_pending_mutation_request_not_from_controller_on_vrs_objects()
    )
}

// just to make Verus happy
pub uninterp spec fn dummy<T>(t: T) -> bool;

#[macro_export]
macro_rules! and {
    ($($tokens:tt)+) => {
        closure_to_fn_spec(|s| {
            and_internal!(s, $($tokens)+)
        })
    };
}

#[macro_export]
macro_rules! and_internal {
    ($s:expr, $head:expr) => {
        $head($s)
    };

    ($s:expr, $head:expr, $($tail:tt)+) => {
        and_internal!($s, $head) && and_internal!($s, $($tail)+)
    };
}

#[macro_export]
macro_rules! or {
    ($($tokens:tt)+) => {
        closure_to_fn_spec(|s| {
            or_internal!(s, $($tokens)+)
        })
    };
}

#[macro_export]
macro_rules! or_internal {
    ($s:expr, $head:expr) => {
        $head($s)
    };

    ($s:expr, $head:expr, $($tail:tt)+) => {
        or_internal!($s, $head) || or_internal!($s, $($tail)+)
    };
}

// usage: at_step![step_or_pred]
// step_or_pred = step | (step, pred)
#[macro_export]
macro_rules! at_step {
    [ $($tokens:tt)? ] => {
        closure_to_fn_spec(|s: ReconcileLocalState| {
            let vds = VDeploymentReconcileState::unmarshal(s).unwrap();
            at_step_or_internal!(vds, $($tokens)?)
        })
    };
}

// usage: at_step_or![step_or_pred,*]
// step_or_pred = step | (step, pred)
#[macro_export]
macro_rules! at_step_or {
    [ $($tokens:tt)+ ] => {
        closure_to_fn_spec(|s: ReconcileLocalState| {
            let vds = VDeploymentReconcileState::unmarshal(s).unwrap();
            at_step_or_internal!(vds, $($tokens)+)
        })
    };
}

#[macro_export]
macro_rules! at_step_or_internal {
    ($vds:expr, ($step:expr, $pred:expr)) => {
        $vds.reconcile_step.eq_step($step) && $pred($vds)
    };

    // eq_step is the tricky workaround for error, see src/controllers/vdeployment_controller/trusted/step.rs
    ($vds:expr, $step:expr) => {
        $vds.reconcile_step.eq_step($step)
    };

    ($vds:expr, $head:tt, $($tail:tt)+) => {
        at_step_or_internal!($vds, $head) || at_step_or_internal!($vds, $($tail)+)
    };
}

// usage: lift_local(controller_id, vd, at_step_or![step_or_pred+])
pub open spec fn lift_local(controller_id: int, vd: VDeploymentView, step_pred: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), step_pred)
}

// hacky workaround for type conversion bug: error[E0605]: non-primitive cast: `{integer}` as `builtin::nat`
#[macro_export]
macro_rules! nat0 {
    () => {
        spec_literal_nat("0")
    };
}

#[macro_export]
macro_rules! nat1 {
    () => {
        spec_literal_nat("1")
    };
}

#[macro_export]
macro_rules! int0 {
    () => {
        spec_literal_int("0")
    };
}

#[macro_export]
macro_rules! int1 {
    () => {
        spec_literal_int("1")
    };
}

pub use nat0;
pub use nat1;
pub use int0;
pub use int1;
pub use at_step_or_internal;
pub use at_step_or;
pub use at_step;
pub use or;
pub use or_internal;
pub use and;
pub use and_internal;

// General helper predicates
pub open spec fn lifted_vd_rely_condition(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    lift_state(|s| {
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] vd_rely(other_id)(s)
    })
}

pub open spec fn lifted_vd_rely_condition_action(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    lift_action(|s, s_prime| {
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] vd_rely(other_id)(s))
        && (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vd_rely(other_id)(s_prime))
    })
}

pub open spec fn lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id: int) -> TempPred<ClusterState> {
    lift_action(|s, s_prime| {
        (forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s))
        && (forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s_prime))
    })
}

pub open spec fn owner_references_contains_ignoring_uid(meta: ObjectMetaView, orig_or: OwnerReferenceView) -> bool {
    exists |or: OwnerReferenceView| {
        &&& #[trigger] meta.owner_references_contains(or)
        &&& or.block_owner_deletion == orig_or.block_owner_deletion
        &&& or.controller == orig_or.controller
        &&& or.kind == orig_or.kind
        &&& or.name == orig_or.name
    }
}

}