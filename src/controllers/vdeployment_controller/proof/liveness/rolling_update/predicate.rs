use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*
};
use crate::vdeployment_controller::{
    trusted::{rely_guarantee::*, step::*, spec_types::*, util::*,
        rely_guarantee::vd_rely, liveness_theorem::*},
    model::{install::*, reconciler::*},
    proof::predicate::*,
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use vstd::prelude::*;

verus! {

pub open spec fn ru_exists_pending_list_resp_in_flight_and_match_req(
    vd: VDeploymentView, controller_id: int, new_vrs_key: ObjectRef
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
            &&& ru_resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s, new_vrs_key)
        }
    }
}

pub open spec fn ru_resp_msg_is_pending_list_resp_in_flight_and_match_req(
    vd: VDeploymentView, controller_id: int, resp_msg: Message, new_vrs_key: ObjectRef
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        // predicate on req_msg, it's not in_flight
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_list_vrs_req(vd, controller_id, req_msg, s)
        // predicate on resp_msg
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& ru_resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s, new_vrs_key)
    }
}

pub open spec fn ru_resp_msg_is_ok_list_resp_containing_matched_vrs(
    vd: VDeploymentView, resp_msg: Message, s: ClusterState, new_vrs_key: ObjectRef
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
        &&& etcd_vrs.metadata.without_resource_version() == vrs.metadata.without_resource_version()
        &&& etcd_vrs.spec == vrs.spec
    }
    &&& exists |vrs| {
        &&& #[trigger] managed_vrs_list.contains(vrs)
        &&& vrs.object_ref() == new_vrs_key
        &&& vrs.status is Some
        &&& vrs.status->0.replicas == vrs.spec.replicas.unwrap_or(1)
    }
}

// glue predicate that connects (new_vrs, n) and resp_objs
pub open spec fn new_vrs_and_no_old_vrs_from_resp_objs(
    vd: VDeploymentView, controller_id: int, resp_msg: Message, nv_uid_key_replicas_status: (Uid, ObjectRef, int, Option<int>), new_vrs_key: ObjectRef
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
        let vrs_list = objects_to_vrs_list(resp_objs)->0;
        let managed_vrs_list = vrs_list.filter(|vrs| valid_owned_vrs(vrs, vd));
        let etcd_vrs = VReplicaSetView::unmarshal(s.resources()[new_vrs_key])->Ok_0;
        &&& resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s)
        &&& {
            let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(vd, managed_vrs_list);
            &&& new_vrs is Some
            &&& new_vrs->0.metadata.uid is Some
            &&& new_vrs->0.metadata.uid->0 == nv_uid_key_replicas_status.0
            &&& new_vrs->0.metadata.name is Some
            &&& new_vrs->0.metadata.namespace is Some
            &&& new_vrs->0.object_ref() == nv_uid_key_replicas_status.1
            &&& get_replicas(new_vrs->0.spec.replicas) == nv_uid_key_replicas_status.2
            &&& if new_vrs->0.status is Some {
                &&& nv_uid_key_replicas_status.3 is Some
                &&& new_vrs->0.status->0.replicas == nv_uid_key_replicas_status.3->0
            } else {
                &&& nv_uid_key_replicas_status.3 is None
            }
            &&& old_vrs_list.len() == 0
            // reasoning on nondeterminism in new vrs choice
            &&& etcd_vrs.spec.replicas.unwrap_or(1) > 0 ==> {
                &&& new_vrs->0.object_ref() == new_vrs_key
                &&& new_vrs->0.metadata.uid->0 == etcd_vrs.metadata.uid->0
                &&& new_vrs->0.spec.replicas.unwrap_or(1) > 0
            }
            &&& new_vrs->0.object_ref() != new_vrs_key ==> {
                &&& new_vrs->0.spec.replicas.unwrap_or(1) == 0
                &&& vd.spec.replicas.unwrap_or(1) == 0
            }
        }
    }
}

// in addition to new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs
pub open spec fn ru_resp_objs_with_new_vrs_status_matching_replicas_and_no_old_vrs(
    vd: VDeploymentView, controller_id: int, resp_msg: Message, nv_uid_key: Option<(Uid, ObjectRef)>
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
        let vrs_list = objects_to_vrs_list(resp_objs)->0;
        let managed_vrs_list = vrs_list.filter(|vrs| valid_owned_vrs(vrs, vd));
        &&& resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s)
        &&& {
            let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(vd, managed_vrs_list);
            &&& new_vrs is Some == nv_uid_key is Some
            &&& new_vrs is Some ==> {
                &&& new_vrs->0.metadata.uid is Some
                &&& new_vrs->0.metadata.uid->0 == (nv_uid_key->0).0
                &&& new_vrs->0.metadata.name is Some
                &&& new_vrs->0.metadata.namespace is Some
                &&& new_vrs->0.status is Some
                &&& new_vrs->0.status->0.replicas == get_replicas(new_vrs->0.spec.replicas)
                &&& new_vrs->0.object_ref() == (nv_uid_key->0).1
                &&& get_replicas(new_vrs->0.spec.replicas) == get_replicas(vd.spec.replicas)
            }
            &&& old_vrs_list.len() == 0
        }
    }
}

// to replace local_state_is_valid_and_coherent_with_etcd
pub open spec fn local_state_at_after_scale_vrs(vd: VDeploymentView, controller_id: int, new_vrs_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let vds = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        let vrs = vds.new_vrs->0;
        let key = vrs.object_ref();
        let etcd_vrs = VReplicaSetView::unmarshal(s.resources()[key])->Ok_0;
        // new vrs is valid
        &&& vds.new_vrs is Some
        &&& vrs.metadata.uid is Some
        &&& vrs.metadata.owner_references is Some
        &&& vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
        &&& valid_owned_vrs(vrs, vd) // used in checks at AfterScaleDownOldVRS
        &&& match_template_without_hash(vd.spec.template)(vrs)
        // new vrs is coherent with etcd state
        &&& s.resources().contains_key(key)
        &&& valid_owned_obj_key(vd, s)(key)
        &&& filter_new_vrs_keys(vd.spec.template, s)(key)
        &&& vrs.object_ref() == key
        &&& etcd_vrs.metadata.without_resource_version() == vrs.metadata.without_resource_version()
        &&& etcd_vrs.spec.without_replicas() == vrs.spec.without_replicas()
        // branch condition for scale_new_vrs
        &&& if get_replicas(vd.spec.replicas) > get_replicas(etcd_vrs.spec.replicas) {
            &&& vrs.spec.replicas == Some(get_replicas(etcd_vrs.spec.replicas) + 1)
        } else if get_replicas(vd.spec.replicas) < get_replicas(etcd_vrs.spec.replicas) {
            &&& vrs.spec.replicas == Some(get_replicas(etcd_vrs.spec.replicas) - 1)
        } else {
            false
        }
    }
}

// ---- Scale-new-vrs-by-one pending/resp predicates ----

pub open spec fn ru_req_msg_is_scale_new_vrs_by_one_req(
    vd: VDeploymentView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req = req_msg.content->APIRequest_0->GetThenUpdateRequest_0;
        let key = req.key();
        let etcd_obj = s.resources()[key];
        let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
        let req_vrs = VReplicaSetView::unmarshal(req.obj)->Ok_0;
        let state = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        let req_vrs_replicas = get_replicas(req_vrs.spec.replicas);
        &&& req_msg.src == HostId::Controller(controller_id, vd.object_ref())
        &&& req_msg.dst == HostId::APIServer
        &&& req_msg.content is APIRequest
        &&& req_msg.content->APIRequest_0 is GetThenUpdateRequest
        &&& VReplicaSetView::unmarshal(req.obj) is Ok
        &&& req.namespace == vd.metadata.namespace->0
        &&& req.owner_ref == vd.controller_owner_ref()
        &&& req_vrs == state.new_vrs->0
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
        &&& etcd_vrs.metadata.without_resource_version() == req_vrs.metadata.without_resource_version()
        &&& req_vrs.spec == VReplicaSetSpecView { // eq w/o replicas
            replicas: Some(req_vrs_replicas),
            ..etcd_vrs.spec
        }
        // owned by vd
        &&& req_vrs.metadata.owner_references is Some
        &&& req_vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
        &&& vd.spec.replicas.unwrap_or(1) > 0 ==> req_vrs.spec.replicas.unwrap_or(1) > 0
        &&& key == req_vrs.object_ref()
        // required by rank_never_increases
        // before the request is applied, it's < or >
        // after it's applied, it's ==
        &&& get_replicas(vd.spec.replicas) > get_replicas(etcd_vrs.spec.replicas) ==> {
            ||| req_vrs_replicas == get_replicas(etcd_vrs.spec.replicas) + 1
            ||| req_vrs_replicas == get_replicas(etcd_vrs.spec.replicas)
        }
        &&& get_replicas(vd.spec.replicas) < get_replicas(etcd_vrs.spec.replicas) ==> {
            ||| req_vrs_replicas == get_replicas(etcd_vrs.spec.replicas) - 1
            ||| req_vrs_replicas == get_replicas(etcd_vrs.spec.replicas)
        }
        // this is unreachable, but necessary for rank_never_increases
        // we need it to prove when n=0 the request won't change replicas
        &&& get_replicas(vd.spec.replicas) == get_replicas(etcd_vrs.spec.replicas)
            ==> req_vrs_replicas == get_replicas(etcd_vrs.spec.replicas)
    }
}

pub open spec fn ru_pending_scale_new_vrs_by_one_req_in_flight(
    vd: VDeploymentView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        let req = req_msg.content->APIRequest_0->GetThenUpdateRequest_0;
        let req_vrs = VReplicaSetView::unmarshal(req.obj)->Ok_0;
        let etcd_obj = s.resources()[req.key()];
        let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& ru_req_msg_is_scale_new_vrs_by_one_req(vd, controller_id, req_msg)(s)
        // stronger: when it's inflight, the new vrs is not scaled yet
        &&& get_replicas(vd.spec.replicas) != get_replicas(etcd_vrs.spec.replicas)
        &&& get_replicas(vd.spec.replicas) > get_replicas(etcd_vrs.spec.replicas)
            ==> get_replicas(req_vrs.spec.replicas) == get_replicas(etcd_vrs.spec.replicas) + 1
        &&& get_replicas(vd.spec.replicas) < get_replicas(etcd_vrs.spec.replicas)
            ==> get_replicas(req_vrs.spec.replicas) == get_replicas(etcd_vrs.spec.replicas) - 1
    }
}

pub open spec fn ru_req_msg_is_pending_scale_new_vrs_by_one_req_in_flight(
    vd: VDeploymentView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req = req_msg.content->APIRequest_0->GetThenUpdateRequest_0;
        let req_vrs = VReplicaSetView::unmarshal(req.obj)->Ok_0;
        let etcd_obj = s.resources()[req.key()];
        let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& ru_req_msg_is_scale_new_vrs_by_one_req(vd, controller_id, req_msg)(s)
        // stronger: when it's inflight, the new vrs is not scaled yet
        &&& get_replicas(vd.spec.replicas) != get_replicas(etcd_vrs.spec.replicas)
        &&& get_replicas(vd.spec.replicas) > get_replicas(etcd_vrs.spec.replicas)
            ==> get_replicas(req_vrs.spec.replicas) == get_replicas(etcd_vrs.spec.replicas) + 1
        &&& get_replicas(vd.spec.replicas) < get_replicas(etcd_vrs.spec.replicas)
            ==> get_replicas(req_vrs.spec.replicas) == get_replicas(etcd_vrs.spec.replicas) - 1
    }
}

}