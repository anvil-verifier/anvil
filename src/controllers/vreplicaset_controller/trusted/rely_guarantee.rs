use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::temporal_logic::defs::*;
use crate::vreplicaset_controller::trusted::spec_types::*;
use vstd::prelude::*;

verus! {

// VRS Rely Condition

// Other controllers don't create pods owned by a VReplicaSet.
pub open spec fn vrs_rely_create_req(req: CreateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == Kind::PodKind ==> !{
            let owner_references = req.obj.metadata.owner_references->0;
            &&& req.obj.metadata.owner_references is Some
            &&& exists |vrs: VReplicaSetView| 
                #[trigger] owner_references.contains(vrs.controller_owner_ref())
        }
    }
}

// Update requests to pods must carry a resource version on them (despite 
// the underlying kind permitting unconditional updates). Also, update requests
// cannot 1) update pods owned by a VReplicaSet, or 2) update pods to become owned
// by a VReplicaSet.
pub open spec fn vrs_rely_update_req(req: UpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == Kind::PodKind ==>
            req.obj.metadata.resource_version is Some
            // Prevents 1): where other controllers update pods already owned
            // by a VReplicaSet.
            && !{
                let etcd_obj = s.resources()[req.key()];
                let owner_references = etcd_obj.metadata.owner_references->0;
                &&& s.resources().contains_key(req.key())
                &&& etcd_obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
                &&& etcd_obj.metadata.owner_references is Some
                &&& exists |vrs: VReplicaSetView| 
                    #[trigger] owner_references.contains(vrs.controller_owner_ref())
            }
            // Prevents 2): where other controllers update pods so they become
            // owned by a VReplicaSet.
            && (req.obj.metadata.owner_references is Some ==>
                    forall |vrs: VReplicaSetView| 
                        ! #[trigger] req.obj.metadata.owner_references->0.contains(vrs.controller_owner_ref()))
    }
}

// Update requests to pods must carry a resource version on them
// and cannot 1) update pods owned by a VReplicaSet
//         or 2) update pod to become owned
// by a VReplicaSet.
pub open spec fn vrs_rely_get_then_update_req(req: GetThenUpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == Kind::PodKind ==> {
            // Prevents 1): where other controllers update pods owned by a VReplicaSet.
            // an object can has multiple owners, but only one controller owner
            // We force requests from other controllers to carry the controller owner reference
            // to achieve exclusive ownerships
            // TODO: add type invariant
            &&& req.owner_ref.controller is Some
            &&& req.owner_ref.controller->0
            &&& req.owner_ref.kind != VReplicaSetView::kind()
            // Prevents 2): where other controllers update pods so they become
            // owned by a VReplicaSet.
            &&& (req.obj.metadata.owner_references is Some ==>
                forall |vrs: VReplicaSetView| 
                    ! req.obj.metadata.owner_references->0.contains(#[trigger] vrs.controller_owner_ref()))
        }
    }
}

// Dealt with similarly to update requests, minus the condition on 
// owner_references.
// TODO: allow other controllers to send UpdateStatus
// requests to owned pods after we address the fairness issues.
pub open spec fn vrs_rely_update_status_req(req: UpdateStatusRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == Kind::PodKind ==> 
            req.obj.metadata.resource_version is Some
            && !{
                let etcd_obj = s.resources()[req.key()];
                let owner_references = etcd_obj.metadata.owner_references->0;
                &&& s.resources().contains_key(req.key())
                &&& etcd_obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
                &&& etcd_obj.metadata.owner_references is Some
                &&& exists |vrs: VReplicaSetView| 
                    #[trigger] owner_references.contains(vrs.controller_owner_ref())
            }
    }
}

// All delete requests to pods carry a precondition on the resource version,
// and other controllers don't try to delete pods owned by a VReplicaSet.
pub open spec fn vrs_rely_delete_req(req: DeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.key.kind == Kind::PodKind ==>
            req.preconditions is Some
            && req.preconditions->0.resource_version is Some
            && !{
                let etcd_obj = s.resources()[req.key];
                let owner_references = etcd_obj.metadata.owner_references->0;
                &&& s.resources().contains_key(req.key)
                &&& etcd_obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version
                    == req.preconditions->0.resource_version
                &&& etcd_obj.metadata.owner_references is Some
                &&& exists |vrs: VReplicaSetView| 
                    #[trigger] owner_references.contains(vrs.controller_owner_ref())
            }
    }
}

// Other controllers don't try to delete pods owned by a VReplicaSet.
pub open spec fn vrs_rely_get_then_delete_req(req: GetThenDeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.key.kind == Kind::PodKind ==> {
            &&& req.owner_ref.controller is Some
            &&& req.owner_ref.controller->0
            &&& req.owner_ref.kind != VReplicaSetView::kind()
        }
    }
}

pub open spec fn vrs_rely(other_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content.is_APIRequest()
            &&& msg.src.is_controller_id(other_id)
        } ==> match msg.content.get_APIRequest_0() {
            APIRequest::CreateRequest(req) => vrs_rely_create_req(req)(s),
            APIRequest::UpdateRequest(req) => vrs_rely_update_req(req)(s),
            APIRequest::GetThenUpdateRequest(req) => vrs_rely_get_then_update_req(req)(s),
            APIRequest::UpdateStatusRequest(req) => vrs_rely_update_status_req(req)(s),
            APIRequest::DeleteRequest(req) => vrs_rely_delete_req(req)(s),
            APIRequest::GetThenDeleteRequest(req) => vrs_rely_get_then_delete_req(req)(s),
            _ => true,
        }
    }
}

// VRS Guarantee Condition

// VRS only creates pods owned by a VReplicaSet.
pub open spec fn vrs_guarantee_create_req(req: CreateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let owner_references = req.obj.metadata.owner_references->0;
        &&& req.obj.kind == Kind::PodKind
        &&& req.obj.metadata.owner_references is Some
        &&& exists |vrs: VReplicaSetView| 
            owner_references == seq![#[trigger] vrs.controller_owner_ref()]
    }
}

// With transactional API, we don't need to check resource version anymore.
// VRS only send delete requests to pods owned by a VReplicaSet.
pub open spec fn vrs_guarantee_get_then_delete_req(req: GetThenDeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& req.key.kind == Kind::PodKind
        &&& exists |vrs: VReplicaSetView| 
            req.owner_ref == #[trigger] vrs.controller_owner_ref()
    }
}

pub open spec fn vrs_guarantee(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content.is_APIRequest()
            &&& msg.src.is_controller_id(controller_id)
        } ==> match msg.content.get_APIRequest_0() {
            APIRequest::ListRequest(_) => true,
            APIRequest::CreateRequest(req) => vrs_guarantee_create_req(req)(s),
            APIRequest::GetThenDeleteRequest(req) => vrs_guarantee_get_then_delete_req(req)(s),
            _ => false, // vrs doesn't send other requests (yet).
        }
    }
}


}
