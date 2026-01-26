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

// CR in ongoing reconciles is coherent with vd in many ways
pub open spec fn at_vd_step_with_vd(vd: VDeploymentView, controller_id: int, step_pred: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
        let local_state = s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state;
        &&& s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
        &&& VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).is_ok()
        &&& VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).is_ok()
        &&& step_pred(local_state)
        &&& {
            &&& helper_invariants::vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)(s)
            // from vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd, we know:
            &&& triggering_cr.controller_owner_ref() == vd.controller_owner_ref()
            &&& (|vrs| valid_owned_vrs(vrs, triggering_cr)) == (|vrs| valid_owned_vrs(vrs, vd))
            &&& (|vrs_list| filter_old_and_new_vrs(vd, vrs_list)) == (|vrs_list| filter_old_and_new_vrs(triggering_cr, vrs_list))
            &&& (|s| valid_owned_obj_key(vd, s)) == (|s| valid_owned_obj_key(triggering_cr, s))
            &&& (|s| filter_obj_keys_managed_by_vd(vd, s)) == (|s| filter_obj_keys_managed_by_vd(triggering_cr, s))
        }
    }
}

pub open spec fn vrs_weakly_eq(lhs: VReplicaSetView, rhs: VReplicaSetView) -> bool {
    &&& lhs.metadata.uid is Some
    &&& lhs.metadata.name is Some
    &&& lhs.metadata.namespace is Some
    &&& lhs.metadata.uid == rhs.metadata.uid
    &&& lhs.metadata.namespace == rhs.metadata.namespace
    &&& lhs.metadata.name == rhs.metadata.name
    &&& lhs.metadata.labels == rhs.metadata.labels
    &&& lhs.metadata.owner_references == rhs.metadata.owner_references
}

// ---- message predicates ----
// we have 2 versions of each predicate because we need to instantiate msg for wf lemmas
// and another exists |msg| is also required as post condition

pub open spec fn no_pending_req_in_cluster(vd: VDeploymentView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        Cluster::no_pending_req_msg(controller_id, s, vd.object_ref())
    }
}

pub open spec fn req_msg_is_list_vrs_req(
    vd: VDeploymentView, controller_id: int, req_msg: Message, s: ClusterState
) -> bool {
    let req = req_msg.content->APIRequest_0;
    &&& req_msg.src == HostId::Controller(controller_id, vd.object_ref())
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content is APIRequest
    &&& req is ListRequest
    &&& req->ListRequest_0 == ListRequest {
        kind: VReplicaSetView::kind(),
        namespace: vd.metadata.namespace.unwrap(),
    }
}

pub open spec fn pending_list_req_in_flight(
    vd: VDeploymentView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_list_vrs_req(vd, controller_id, req_msg, s)
    }
}

pub open spec fn req_msg_is_pending_list_req_in_flight(
    vd: VDeploymentView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_list_vrs_req(vd, controller_id, req_msg, s)
    }
}

// should be used with VReplicaSetView::marshal_preserves_integrity()
// resp is list resp matching req && resp content match etcd
pub open spec fn exists_pending_list_resp_in_flight_and_match_req(
    vd: VDeploymentView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        // predicate on req_msg, it's not in_flight
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_list_vrs_req(vd, controller_id, req_msg, s)
        // predicate on resp_msg
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg_is_ok_list_resp_containing_matched_vrs(vd, controller_id, resp_msg, s)
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
        &&& req_msg_is_list_vrs_req(vd, controller_id, req_msg, s)
        // predicate on resp_msg
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg_is_ok_list_resp_containing_matched_vrs(vd, controller_id, resp_msg, s)
    }
}

/* Notes about objects(vrs) ownership:
the current version of valid_owned_vrs is confusing, and it couples the exec and proof parts, we should separate them when needed
Ideally, we only need the namespace to match and vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
    and the equality with vrs.metadata.owner_references_contains(vd.controller_owner_ref()) can be proved using each_object_in_etcd_has_at_most_one_controller_owner
The unmarshallability part can be proved using each_custom_object_in_etcd_is_well_formed
*/

pub open spec fn resp_msg_is_ok_list_resp_containing_matched_vrs(
    vd: VDeploymentView, controller_id: int, resp_msg: Message, s: ClusterState
) -> bool {
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    let vrs_list = objects_to_vrs_list(resp_objs)->0;
    let managed_vrs_list = vrs_list.filter(|vrs| valid_owned_vrs(vrs, vd));
    &&& resp_msg.content.is_list_response()
    &&& resp_msg.content.get_list_response().res is Ok
    &&& objects_to_vrs_list(resp_objs) is Some
    &&& resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref()).no_duplicates()
    &&& managed_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref()).to_set()
        == filter_obj_keys_managed_by_vd(vd, s)
    &&& forall |obj: DynamicObjectView| #[trigger] resp_objs.contains(obj) ==> {
        &&& VReplicaSetView::unmarshal(obj) is Ok
        &&& obj.metadata.namespace is Some
        &&& obj.metadata.name is Some
        &&& obj.metadata.uid is Some
    }
    &&& forall |vrs: VReplicaSetView| #[trigger] managed_vrs_list.contains(vrs) ==> {
        let key = vrs.object_ref();
        let etcd_obj = s.resources()[key];
        let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
        // strengthen valid_owned_vrs, as only one controller owner is allowed
        &&& vrs.metadata.owner_references is Some
        &&& vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
        &&& valid_owned_vrs(vrs, vd)
        &&& s.resources().contains_key(key)
        &&& VReplicaSetView::unmarshal(etcd_obj) is Ok
        // weakly equal to etcd object
        &&& valid_owned_obj_key(vd, s)(key)
        &&& vrs_weakly_eq(etcd_vrs, vrs)
        &&& etcd_vrs.spec == vrs.spec
    }
}

// glue predicate that connects (new_vrs, n) and resp_objs
pub open spec fn new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(
    vd: VDeploymentView, controller_id: int, resp_msg: Message, nv_uid_key_replicas: Option<(Uid, ObjectRef, int)>, n: nat
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
        let vrs_list = objects_to_vrs_list(resp_objs)->0;
        let managed_vrs_list = vrs_list.filter(|vrs| valid_owned_vrs(vrs, vd));
        &&& resp_msg_is_ok_list_resp_containing_matched_vrs(vd, controller_id, resp_msg, s)
        &&& {
            let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(vd, managed_vrs_list);
            &&& new_vrs is Some == nv_uid_key_replicas is Some
            &&& new_vrs is Some ==> {
                &&& new_vrs->0.metadata.uid is Some
                &&& new_vrs->0.metadata.uid->0 == (nv_uid_key_replicas->0).0
                &&& new_vrs->0.metadata.name is Some
                &&& new_vrs->0.metadata.namespace is Some
                &&& new_vrs->0.object_ref() == (nv_uid_key_replicas->0).1
                &&& get_replicas(new_vrs->0.spec.replicas) == (nv_uid_key_replicas->0).2
            }
            &&& old_vrs_list.len() == n
        }
    }
}

// because make_replica_set use vd's RV to fake hash
// we need to use triggering_cr here as a temporary workaround
// because vd only provides basic spec, and has no RV
pub open spec fn req_msg_is_create_vrs_req(
    vd: VDeploymentView, controller_id: int, req_msg: Message, s: ClusterState
) -> bool {
    let req = req_msg.content->APIRequest_0->CreateRequest_0;
    let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
    &&& req_msg.src == HostId::Controller(controller_id, vd.object_ref())
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content is APIRequest
    &&& req_msg.content->APIRequest_0 is CreateRequest
    &&& req == CreateRequest {
        namespace: vd.metadata.namespace.unwrap(),
        obj: make_replica_set(triggering_cr).marshal() // vd doesn't have rv
    }
}

pub open spec fn pending_create_new_vrs_req_in_flight(
    vd: VDeploymentView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_create_vrs_req(vd, controller_id, req_msg, s)
    }
}

pub open spec fn req_msg_is_pending_create_new_vrs_req_in_flight(
    vd: VDeploymentView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {  
    |s: ClusterState| {
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_create_vrs_req(vd, controller_id, req_msg, s)
    }
}

pub open spec fn resp_msg_is_ok_create_new_vrs_resp(
    vd: VDeploymentView, controller_id: int, resp_msg: Message, nv_uid_key: (Uid, ObjectRef)
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_create_vrs_req(vd, controller_id, req_msg, s)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg_is_ok_create_resp_containing_new_vrs(vd, controller_id, resp_msg, nv_uid_key, s)
    }
}

// etcd_state_is and local_state_is_valid_and_coherent_with_etcd are included to share the quantifier
pub open spec fn exists_create_resp_msg_containing_new_vrs_uid_key(
    vd: VDeploymentView, controller_id: int, n: nat
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_create_vrs_req(vd, controller_id, req_msg, s)
        &&& exists |j: (Message, (Uid, ObjectRef))| {
            // predicate on resp_msg
            &&& #[trigger] s.in_flight().contains(j.0)
            &&& resp_msg_matches_req_msg(j.0, req_msg)
            // we don't need info on content of the response at the moment
            &&& #[trigger] resp_msg_is_ok_create_resp_containing_new_vrs(vd, controller_id, j.0, j.1, s)
            &&& etcd_state_is(vd, controller_id, Some(((j.1).0, (j.1).1, get_replicas(vd.spec.replicas))), n)(s)
        }
    }
}

pub open spec fn resp_msg_is_ok_create_resp_containing_new_vrs(
    vd: VDeploymentView, controller_id: int, resp_msg: Message, nv_uid_key: (Uid, ObjectRef), s: ClusterState
) -> bool {
    let (uid, key) = nv_uid_key;
    let vds = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    let resp_obj = resp_msg.content.get_create_response().res.unwrap();
    let vrs = VReplicaSetView::unmarshal(resp_obj)->Ok_0;
    let etcd_obj = s.resources()[key];
    let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
    &&& resp_msg.content.is_create_response()
    &&& resp_msg.content.get_create_response().res is Ok
    &&& VReplicaSetView::unmarshal(resp_obj) is Ok
    &&& vrs.object_ref() == key
    &&& vrs.metadata.uid is Some
    &&& vrs.metadata.uid->0 == uid
    // strengthen valid_owned_vrs, as only one controller owner is allowed
    &&& vrs.metadata.owner_references is Some
    &&& vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
    &&& vrs.spec.replicas.unwrap_or(1) == vd.spec.replicas.unwrap_or(1)
    // this combined with all above ==> valid_owned_vrs
    &&& vrs.metadata.deletion_timestamp is None
    &&& s.resources().contains_key(key)
    // weakly equal to etcd object
    &&& valid_owned_obj_key(vd, s)(key)
    &&& filter_new_vrs_keys(vd.spec.template, s)(key)
    &&& vrs_weakly_eq(etcd_vrs, vrs)
    &&& etcd_vrs.spec == vrs.spec
    // new_vrs uid does not match any old_vrs uid. TODO: find a better way to not talk about local state
    &&& forall |i| #![trigger vds.old_vrs_list[i]] 0 <= i < vds.old_vrs_list.len() ==>
        vds.old_vrs_list[i].metadata.uid->0 != uid && vds.old_vrs_list[i].object_ref() != key
}

pub open spec fn req_msg_is_scale_old_vrs_req(
    vd: VDeploymentView, controller_id: int, req_msg: Message, nv_uid: Uid, pre_update: bool
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req = req_msg.content->APIRequest_0->GetThenUpdateRequest_0;
        let key = req.key();
        let etcd_obj = s.resources()[key];
        let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
        let req_vrs = VReplicaSetView::unmarshal(req.obj)->Ok_0;
        let state = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        let local_vrs = state.old_vrs_list[state.old_vrs_index as int];
        &&& req_msg.src == HostId::Controller(controller_id, vd.object_ref())
        &&& req_msg.dst == HostId::APIServer
        &&& req_msg.content is APIRequest
        &&& req_msg.content->APIRequest_0 is GetThenUpdateRequest
        &&& VReplicaSetView::unmarshal(req.obj) is Ok
        &&& req.namespace == vd.metadata.namespace->0
        &&& req.owner_ref == vd.controller_owner_ref()
        &&& valid_owned_vrs(req_vrs, vd)
        // can pass filter_old_vrs_keys if we ignore replicas
        &&& req_vrs.metadata.uid is Some
        &&& req_vrs.metadata.uid->0 != nv_uid
        // etcd obj is owned by vd and should be protected by non-interference property
        &&& s.resources().contains_key(key)
        &&& valid_owned_obj_key(vd, s)(key)
        // the scaled down vrs can previously pass old vrs filter
        &&& vrs_weakly_eq(etcd_vrs, req_vrs)
        // owned by vd
        &&& req_vrs.metadata.owner_references is Some
        &&& req_vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
        // scaled down vrs should not pass old vrs filter in s_prime
        &&& req_vrs.spec.replicas == Some(int0!())
        // stronger than local_state_is_valid_and_coherent_with_etcd
        &&& state.old_vrs_index < state.old_vrs_list.len()
        // of course, replica isn't updated locally
        &&& vrs_weakly_eq(req_vrs, local_vrs)
        // this is important, then we know etcd_vrs can pass old_vrs_filter from the coherence predicate
        &&& pre_update ==> etcd_vrs.spec.replicas.unwrap_or(1) > 0
        // derive from no_duplicates(), coherence isn't affected
        &&& forall |i: int| #![trigger state.old_vrs_list[i]] 0 <= i < state.old_vrs_index ==>
            state.old_vrs_list[i].object_ref() != key
        &&& key == local_vrs.object_ref()
        &&& key == req_vrs.object_ref()
    }
}

pub open spec fn req_msg_is_scale_new_vrs_req(
    vd: VDeploymentView, controller_id: int, req_msg: Message, nv_uid_key: (Uid, ObjectRef)
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req = req_msg.content->APIRequest_0->GetThenUpdateRequest_0;
        let key = req.key();
        let etcd_obj = s.resources()[key];
        let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
        let req_vrs = VReplicaSetView::unmarshal(req.obj)->Ok_0;
        let state = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        &&& req_msg.src == HostId::Controller(controller_id, vd.object_ref())
        &&& req_msg.dst == HostId::APIServer
        &&& req_msg.content is APIRequest
        &&& req_msg.content->APIRequest_0 is GetThenUpdateRequest
        &&& VReplicaSetView::unmarshal(req.obj) is Ok
        &&& req.namespace == vd.metadata.namespace->0
        &&& req.owner_ref == vd.controller_owner_ref()
        // so old vrs will not get affected, used as barrier for lemma_scale_new_vrs_req_returns_ok
        &&& req_vrs.metadata.uid->0 == nv_uid_key.0
        &&& req_vrs.object_ref() == nv_uid_key.1
        // updated vrs is valid and owned by vd
        &&& valid_owned_vrs(req_vrs, vd)
        // and can pass new vrs filter
        &&& match_template_without_hash(vd.spec.template)(req_vrs)
        // etcd obj is owned by vd and should be protected by non-interference property
        &&& s.resources().contains_key(key)
        &&& valid_owned_obj_key(vd, s)(key)
        // the scaled down vrs can previously pass new vrs filter
        //// Q: do we really need this?
        // &&& filter_new_vrs_keys(vd.spec.template, s)(key)
        // spec hasn't been updated here
        &&& vrs_weakly_eq(etcd_vrs, req_vrs)
        // owned by vd
        &&& req_vrs.metadata.owner_references is Some
        &&& req_vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
        // scaled down vrs should not pass old vrs filter in s_prime
        &&& req_vrs.spec.replicas == Some(vd.spec.replicas.unwrap_or(1))
        &&& key == state.new_vrs->0.object_ref()
        &&& key == req_vrs.object_ref()
    }
}

pub open spec fn req_msg_is_pending_scale_old_vrs_req_in_flight(
    vd: VDeploymentView, controller_id: int, req_msg: Message, nv_uid: Uid
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_scale_old_vrs_req(vd, controller_id, req_msg, nv_uid, true)(s)
    }
}

pub open spec fn req_msg_is_pending_scale_new_vrs_req_in_flight(
    vd: VDeploymentView, controller_id: int, req_msg: Message, nv_uid_key: (Uid, ObjectRef)
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_scale_new_vrs_req(vd, controller_id, req_msg, nv_uid_key)(s)
    }
}

pub open spec fn pending_scale_old_vrs_req_in_flight(
    vd: VDeploymentView, controller_id: int, nv_uid: Uid
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_scale_old_vrs_req(vd, controller_id, req_msg, nv_uid, true)(s)
    }
}

pub open spec fn pending_scale_new_vrs_req_in_flight(
    vd: VDeploymentView, controller_id: int, nv_uid_key: (Uid, ObjectRef)
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_scale_new_vrs_req(vd, controller_id, req_msg, nv_uid_key)(s)
    }
}

pub open spec fn resp_msg_is_ok_scale_old_vrs_resp_in_flight(
    vd: VDeploymentView, controller_id: int, resp_msg: Message, nv_uid: Uid
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_scale_old_vrs_req(vd, controller_id, req_msg, nv_uid, false)(s)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg.content.get_get_then_update_response().res is Ok
    }
}

pub open spec fn resp_msg_is_ok_scale_new_vrs_resp_in_flight(
    vd: VDeploymentView, controller_id: int, resp_msg: Message, nv_uid_key: (Uid, ObjectRef)
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_scale_new_vrs_req(vd, controller_id, req_msg, nv_uid_key)(s)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg.content.get_get_then_update_response().res is Ok
    }
}

pub open spec fn exists_resp_msg_is_ok_scale_old_vrs_resp_in_flight(
    vd: VDeploymentView, controller_id: int, nv_uid: Uid
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_scale_old_vrs_req(vd, controller_id, req_msg, nv_uid, false)(s)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_then_update_response().res is Ok
        }
    }
}

pub open spec fn exists_resp_msg_is_ok_scale_new_vrs_resp_in_flight(
    vd: VDeploymentView, controller_id: int, nv_uid_key: (Uid, ObjectRef)
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_scale_new_vrs_req(vd, controller_id, req_msg, nv_uid_key)(s)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_then_update_response().res is Ok
        }
    }
}

// we don't need new_vrs.spec.replicas here as local state is enough to differentiate different transitions
pub open spec fn etcd_state_is(vd: VDeploymentView, controller_id: int, nv_uid_key_replicas: Option<(Uid, ObjectRef, int)>, n: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let new_vrs_uid = if nv_uid_key_replicas is Some { Some((nv_uid_key_replicas->0).0) } else { None };
        &&& match nv_uid_key_replicas {
            Some((uid, key, replicas)) => {
                let etcd_obj = s.resources()[key];
                let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
                &&& s.resources().contains_key(key)
                &&& valid_owned_obj_key(vd, s)(key)
                &&& filter_new_vrs_keys(vd.spec.template, s)(key)
                &&& etcd_vrs.metadata.uid is Some
                &&& etcd_vrs.metadata.uid->0 == uid
                &&& etcd_vrs.spec.replicas.unwrap_or(1) == replicas
            },
            None => {
                &&& !exists |k: ObjectRef| {
                    &&& #[trigger] s.resources().contains_key(k)
                    &&& valid_owned_obj_key(vd, s)(k)
                    &&& filter_new_vrs_keys(vd.spec.template, s)(k)
                }
            }
        }
        &&& filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(new_vrs_uid, s)).len() == n
    }
}

pub open spec fn instantiated_etcd_state_is_with_zero_old_vrs(vd: VDeploymentView, controller_id: int)
-> StatePred<ClusterState> {
    |s: ClusterState| exists |nv_uid_key: (Uid, ObjectRef)| {
        &&& #[trigger] etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, get_replicas(vd.spec.replicas))), 0)(s)
    }
}

// make verus happy about triggers, otherwise:
// error: triggers cannot contain let/forall/exists/lambda/choose
//    --> verus/source/target-verus/release/vstd/std_specs/option.rs:194:9
//     |
// 194 |         Some(t) => t,
pub open spec fn get_replicas(i: Option<int>) -> int {
    i.unwrap_or(int1!())
}

// when coherence breaks
pub enum SpecialCase {
    None,
    NewVRSCreated,
    NewVRSReplicaUpdated,
}

// local state matches description by arguments
pub open spec fn local_state_is(
    vd: VDeploymentView, controller_id: int, nv_uid_key_replicas: Option<(Uid, ObjectRef, int)>, n: nat
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let vds = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        &&& vds.old_vrs_index == n
        &&& match nv_uid_key_replicas {
            Some((uid, key, _)) => {
                let new_vrs = vds.new_vrs->0;
                // new vrs in local cache exists and its fingerprint matchesnew_vrs
                &&& vds.new_vrs is Some
                &&& new_vrs.object_ref() == key
                &&& new_vrs.metadata.uid->0 == uid
            },
            None => {
                &&& vds.new_vrs is None
            }
        }
    }
}

pub open spec fn local_state_is_valid_and_coherent_with_etcd(vd: VDeploymentView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& local_state_is_coherent_with_etcd(vd, controller_id)(s)
        &&& local_state_is_valid(vd, controller_id)(s)
    }
}

// coherence: weakly equal to etcd object
pub open spec fn local_state_is_coherent_with_etcd(vd: VDeploymentView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let vds = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        &&& forall |i| #![trigger vds.old_vrs_list[i].object_ref()] 0 <= i < vds.old_vrs_list.len() ==> {
            let vrs = vds.old_vrs_list[i];
            let etcd_vrs = VReplicaSetView::unmarshal(s.resources()[vrs.object_ref()])->Ok_0;
            &&& s.resources().contains_key(vrs.object_ref())
            &&& valid_owned_obj_key(vd, s)(vrs.object_ref())
            &&& vrs_weakly_eq(etcd_vrs, vrs)
        }
        &&& forall |i| #![trigger vds.old_vrs_list[i]] 0 <= i < vds.old_vrs_index ==> {
            let vrs = vds.old_vrs_list[i];
            let etcd_vrs = VReplicaSetView::unmarshal(s.resources()[vrs.object_ref()])->Ok_0;
            &&& etcd_vrs.spec == vrs.spec
        }
        &&& vds.new_vrs is Some ==> {
            let vrs = vds.new_vrs->0;
            // etcd obj exists
            let key = vrs.object_ref();
            let etcd_vrs = VReplicaSetView::unmarshal(s.resources()[key])->Ok_0;
            &&& s.resources().contains_key(key)
            &&& valid_owned_obj_key(vd, s)(key)
            &&& filter_new_vrs_keys(vd.spec.template, s)(key)
            &&& vrs.object_ref() == key
            &&& vrs_weakly_eq(etcd_vrs, vrs)
            // we don't need to check unless MaxSurge | MaxUnavailable is supported
            // &&& etcd_vrs.spec == new_vrs.spec
        }
    }
}

// validity
pub open spec fn local_state_is_valid(vd: VDeploymentView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let vds = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        &&& 0 <= vds.old_vrs_index <= vds.old_vrs_list.len()
        &&& vds.old_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref()).no_duplicates()
        &&& forall |i| #![trigger vds.old_vrs_list[i]] 0 <= i < vds.old_vrs_list.len() ==> {
            let vrs = vds.old_vrs_list[i];
            &&& vrs.metadata.uid is Some
            // is owned by vd
            &&& vrs.metadata.owner_references is Some
            &&& vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
            &&& valid_owned_vrs(vrs, vd) // used in checks at AfterScaleDownOldVRS
            // can pass old vrs filter
            &&& vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0
            // does not have the same uid as new_vrs
            // can pass old vrs filter, so we can infer filter_old_vrs_keys
            // the reason we don't use filter_old_vrs_keys directly in the quantifier below is
            // when the scale down request is in flight, old_vrs_list[old_vrs_index] is not covered
            // then we need to introduce another special case with extra complexity
            &&& vds.new_vrs is Some ==> {
                &&& vrs.metadata.uid->0 != vds.new_vrs->0.metadata.uid->0
                &&& vrs.object_ref() != vds.new_vrs->0.object_ref()
            }
        }
        &&& vds.new_vrs is Some ==> {
            let vrs = vds.new_vrs->0;
            &&& vrs.metadata.uid is Some
            // is owned by vd
            &&& vrs.metadata.owner_references is Some
            &&& vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
            &&& valid_owned_vrs(vrs, vd) // used in checks at AfterScaleDownOldVRS
        }
    }
}

pub open spec fn old_vrs_list_len(n: nat) -> spec_fn(VDeploymentReconcileState) -> bool {
    |vds: VDeploymentReconcileState| vds.old_vrs_index == n
}

pub open spec fn vd_rely_condition(cluster: Cluster, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| forall |other_id| other_id != controller_id && cluster.controller_models.contains_key(other_id)
                                        ==> #[trigger] vd_rely(other_id)(s)
}

pub open spec fn vd_reconcile_request_only_interferes_with_itself_condition(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
}

// same as vrs, similar to rely condition. Yet we talk about owner_ref here
pub open spec fn garbage_collector_does_not_delete_vd_pods(vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src is BuiltinController
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
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
        Cluster::etcd_objects_have_unique_uids(),
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
        Cluster::no_pending_request_to_api_server_from_non_controllers(),
        desired_state_is(vd),
        Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vd.object_ref()),
        helper_invariants::no_other_pending_request_interferes_with_vd_reconcile(vd, controller_id),
        
        // we use lifted version for vd_reconcile_request_only_interferes_with_itself with quantifiers
        helper_invariants::garbage_collector_does_not_delete_vd_vrs_objects(vd),
        helper_invariants::every_msg_from_vd_controller_carries_vd_key(controller_id),
        helper_invariants::vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id),
        helper_invariants::vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)
    )
}

// just to make Verus happy
pub uninterp spec fn dummy<T>(t: T) -> bool;

// General helper predicates
pub open spec fn lifted_vd_rely_condition(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    lift_state(|s| {
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] vd_rely(other_id)(s)
    })
}

// TODO: deprecate this
pub open spec fn lifted_vd_rely_condition_action(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    lift_action(|s, s_prime| {
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] vd_rely(other_id)(s))
        && (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vd_rely(other_id)(s_prime))
    })
}

pub open spec fn lifted_vd_reconcile_request_only_interferes_with_itself(controller_id: int) -> TempPred<ClusterState> {
    lift_state(|s| {
        forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
    })
}

// TODO: deprecate this
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