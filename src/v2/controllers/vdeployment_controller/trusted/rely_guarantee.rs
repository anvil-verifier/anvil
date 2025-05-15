use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::temporal_logic::defs::*;
use crate::vdeployment_controller::trusted::spec_types::*;
use vstd::prelude::*;

verus! {

// VD Rely Condition

// Other controllers don't create VRS owned by a VDeployment.
pub open spec fn vd_rely_create_req(req: CreateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == Kind::CustomResourceKind("vreplicaset"@) ==> !{
            let owner_references = req.obj.metadata.owner_references.get_Some_0();
            &&& req.obj.metadata.owner_references.is_Some()
            &&& exists |vd: VDeploymentView| 
                #[trigger] owner_references.contains(vd.controller_owner_ref())
        }
    }
}

// Update requests to vrs must carry a resource version on them
// and cannot 1) update vrs owned by a VDeployment
//         or 2) update vrs to become owned
// by a VDeployment.
pub open spec vd_rely_update_req(req: UpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == Kind::CustomResourceKind("vreplicaset"@) ==>
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

// TODO: double check if only vrs can send update status req to itself
//       the update to VRS's guarantee to support this should also be updated
// similar to update requests, minus the condition on owner_references.
// Q: how to get controller type in ClusterState?
pub open spec fn vd_rely_update_status_req(req: UpdateStatusRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == Kind::CustomResourceKind("vreplicaset"@) ==> 
            req.obj.metadata.resource_version.is_Some()
            && !{
                let etcd_obj = s.resources()[req.key()];
                &&& s.resources().contains_key(req.key())
                &&& etcd_obj.metadata.resource_version.is_Some()
                &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
            }
    }
}

// All delete requests to vrs carry a precondition on the resource version,
// and other controllers don't try to delete vrs owned by a VDeployment.
pub open spec fn vd_rely_delete_req(req: DeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.key.kind == Kind::CustomResourceKind("vreplicaset"@) ==>
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
                &&& exists |vrs: VReplicaSetView| 
                    #[trigger] owner_references.contains(vrs.controller_owner_ref())
            }
    }
}

pub open spec fn vd_reply(other_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content.is_APIRequest()
            &&& msg.src == HostId::Controller(other_id)
        } => match msg.content.get_APIRequest_0() {
            APIRequest::CreateRequest(req) => vd_rely_create_req(req),
            APIRequest::UpdateRequest(req) => vd_rely_update_req(req),
            APIRequest::UpdateStatusRequest(req) => vd_rely_update_status_req(req),
            APIRequest::DeleteRequest(req) => vd_rely_delete_req(req),
            _ => true,
        }
    }
}

// VD Guarantee Condition

// VD only creates VRS owned by itself.
pub open spec fn vd_guarantee_create_req(req: CreateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& req.obj.kind == Kind::CustomResourceKind("vreplicaset"@)
        &&& req.obj.metadata.owner_references.is_Some()
        &&& exists |vd: VDeploymentView| 
            req.obj.metadata.owner_references.get_Some_0() == seq![#[trigger] vd.controller_owner_ref()]
    }
}

// VD only updates VRS owned by itself.
pub open spec fn vd_guarantee_update_req(req: UpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let etcd_obj = s.resources()[req.key()];
        &&& req.obj.kind == Kind::CustomResourceKind("vreplicaset"@)
        &&& req.obj.metadata.resource_version.is_Some()
        &&& exists |vd: VDeploymentView| 
            req.obj.metadata.owner_references.get_Some_0() == seq![#[trigger] vd.controller_owner_ref()]
    }
}

// TODO: support delete requests (not yet implemented in the controller)
// This should be the same as vrs_guarantee_delete_req
// plus vd will not delete new vrs (has same template as vd)
//      and will not delete when the number of vrs is not greater than vd.Spec.RevisionHistoryLimit
pub open spec fn vd_guarantee_delete_req(req: DeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        true
    }
}

pub open spec fn vd_guarantee(other_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content.is_APIRequest()
            &&& msg.src == HostId::Controller(other_id)
        } => match msg.content.get_APIRequest_0() {
            APIRequest::CreateRequest(req) => vd_guarantee_create_req(req),
            APIRequest::UpdateRequest(req) => vd_guarantee_update_req(req),
            APIRequest::DeleteRequest(req) => vd_guarantee_delete_req(req),
            _ => false, // vd doesn't send other requests
        }
    }
}

}