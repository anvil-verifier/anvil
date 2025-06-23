use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::temporal_logic::defs::*;
use crate::vdeployment_controller::trusted::spec_types::*;
use crate::vreplicaset_controller::trusted::spec_types::*;
use vstd::prelude::*;

verus! {

// VD Rely Condition

// Other controllers don't create VRS owned by a VDeployment.
pub open spec fn vd_rely_create_req(req: CreateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == VReplicaSetView::kind() ==> !{
            let owner_references = req.obj.metadata.owner_references.get_Some_0();
            &&& req.obj.metadata.owner_references.is_Some()
            &&& exists |vd: VDeploymentView| 
                #[trigger] owner_references.contains(vd.controller_owner_ref())
        }
    }
}

// As update is not fully deprecated we need to consider it, same applies to delete
pub open spec fn vd_rely_update_req(req: UpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == VReplicaSetView::kind() ==>
            req.obj.metadata.resource_version.is_Some()
            // Prevents 1): where other controllers update vrs already owned
            // by a VDeployment.
            && !{
                let etcd_obj = s.resources()[req.key()];
                let owner_references = etcd_obj.metadata.owner_references.get_Some_0();
                &&& s.resources().contains_key(req.key())
                &&& etcd_obj.metadata.resource_version.is_Some()
                &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
                &&& etcd_obj.metadata.owner_references.is_Some()
                &&& exists |vd: VDeploymentView| 
                    #[trigger] owner_references.contains(vd.controller_owner_ref())
            }
            // Prevents 2): where other controllers update vrs so they become
            // owned by a VDeployment.
            && (req.obj.metadata.owner_references.is_Some() ==>
                    forall |vd: VDeploymentView| 
                        ! #[trigger] req.obj.metadata.owner_references.get_Some_0().contains(vd.controller_owner_ref()))
    }
}

// Update requests to vrs must carry a resource version on them
// and cannot 1) update vrs owned by a VDeployment
//         or 2) update vrs to become owned
// by a VDeployment.
pub open spec fn vd_rely_get_then_update_req(req: GetThenUpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == VReplicaSetView::kind() ==> {
            // Prevents 1): where other controllers update vrs owned by a VDeployment.
            // an object can has multiple owners, but only one controller owner
            // We force requests from other controllers to carry the controller owner reference
            // to achieve exclusive ownerships
            // TODO: add type invariant
            &&& req.owner_ref.controller.is_Some()
            &&& req.owner_ref.controller.get_Some_0()
            &&& req.owner_ref.kind != VDeploymentView::kind()
            // Prevents 2): where other controllers update vrs so they become
            // owned by a VDeployment.
            &&& (req.obj.metadata.owner_references.is_Some() ==>
                forall |vd: VDeploymentView| 
                    ! req.obj.metadata.owner_references.get_Some_0().contains(vd.controller_owner_ref()))
        }
    }
}

// TODO: double check if only vrs can send update status req to itself
//       the update to VRS's guarantee to support this should also be updated
// similar to update requests, minus the condition on owner_references.
pub open spec fn vd_rely_update_status_req(req: UpdateStatusRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == VDeploymentView::kind() ==> 
            req.obj.metadata.resource_version.is_Some()
            && !{
                let etcd_obj = s.resources()[req.key()];
                &&& s.resources().contains_key(req.key())
                &&& etcd_obj.metadata.resource_version.is_Some()
                &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
            }
    }
}

pub open spec fn vd_rely_delete_req(req: DeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.key.kind == VReplicaSetView::kind() ==>
            req.preconditions.is_Some()
            && req.preconditions.get_Some_0().resource_version.is_Some()
            && !{
                let etcd_obj = s.resources()[req.key];
                let owner_references = etcd_obj.metadata.owner_references.get_Some_0();
                &&& s.resources().contains_key(req.key)
                &&& etcd_obj.metadata.resource_version.is_Some()
                &&& etcd_obj.metadata.resource_version
                    == req.preconditions.get_Some_0().resource_version
                &&& etcd_obj.metadata.owner_references.is_Some()
                &&& exists |vd: VDeploymentView| 
                    #[trigger] owner_references.contains(vd.controller_owner_ref())
            }
    }
}

// Other controllers don't try to delete vrs owned by a VDeployment.
pub open spec fn vd_rely_get_then_delete_req(req: GetThenDeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.key.kind == VReplicaSetView::kind() ==> {
            &&& req.owner_ref.controller.is_Some()
            &&& req.owner_ref.controller.get_Some_0()
            &&& req.owner_ref.kind != VDeploymentView::kind()
        }
    }
}

pub open spec fn vd_rely(other_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content.is_APIRequest()
            &&& msg.src.is_controller_id(other_id)
        } ==> match msg.content.get_APIRequest_0() {
            APIRequest::CreateRequest(req) => vd_rely_create_req(req)(s),
            APIRequest::UpdateRequest(req) => vd_rely_update_req(req)(s),
            APIRequest::GetThenUpdateRequest(req) => vd_rely_get_then_update_req(req)(s),
            APIRequest::UpdateStatusRequest(req) => vd_rely_update_status_req(req)(s),
            APIRequest::DeleteRequest(req) => vd_rely_delete_req(req)(s),
            APIRequest::GetThenDeleteRequest(req) => vd_rely_get_then_delete_req(req)(s),
            _ => true,
        }
    }
}

// VD Guarantee Condition

// VD only creates VRS owned by itself.
pub open spec fn vd_guarantee_create_req(req: CreateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& req.obj.kind == VReplicaSetView::kind()
        &&& req.obj.metadata.owner_references.is_Some()
        &&& exists |vd: VDeploymentView| 
            req.obj.metadata.owner_references.get_Some_0() == seq![#[trigger] vd.controller_owner_ref()]
    }
}

// VD only updates VRS owned by itself.
pub open spec fn vd_guarantee_get_then_update_req(req: GetThenUpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let etcd_obj = s.resources()[req.key()];
        &&& req.obj.kind == VReplicaSetView::kind()
        &&& exists |vd: VDeploymentView|
            req.owner_ref == vd.controller_owner_ref()
            && req.obj.metadata.owner_references_contains(vd.controller_owner_ref())
    }
}

// TODO: support delete requests (not yet implemented in the controller)
// This should be the same as vrs_guarantee_delete_req
// plus vd will not delete new vrs (has same template as vd)
//      and will not delete when the number of vrs is not greater than vd.Spec.RevisionHistoryLimit
pub open spec fn vd_guarantee_get_then_delete_req(req: GetThenDeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        false
    }
}

pub open spec fn vd_guarantee(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content.is_APIRequest()
            &&& msg.src.is_controller_id(controller_id)
        } ==> match msg.content.get_APIRequest_0() {
            APIRequest::CreateRequest(req) => vd_guarantee_create_req(req)(s),
            APIRequest::GetThenUpdateRequest(req) => vd_guarantee_get_then_update_req(req)(s),
            APIRequest::GetThenDeleteRequest(req) => vd_guarantee_get_then_delete_req(req)(s),
            _ => false, // vd doesn't send other requests
        }
    }
}

}