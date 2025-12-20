use crate::kubernetes_api_objects::spec::{prelude::*, persistent_volume_claim::*};
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::vstatefulset_controller::trusted::spec_types::*;
use vstd::prelude::*;

verus! {

// VSTS Rely Condition

pub open spec fn vsts_rely(other_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(other_id)
        } ==> match (msg.content->APIRequest_0) {
            APIRequest::CreateRequest(req) => !interfere_create_pod_req(req)(s),
            APIRequest::UpdateRequest(req) => vd_rely_update_req(req)(s),
            APIRequest::GetThenUpdateRequest(req) => vd_rely_get_then_update_req(req)(s),
            APIRequest::UpdateStatusRequest(req) => vd_rely_update_status_req(req)(s),
            APIRequest::DeleteRequest(req) => vd_rely_delete_req(req)(s),
            APIRequest::GetThenDeleteRequest(req) => vd_rely_get_then_delete_req(req)(s),
            _ => true,
        }
    }
}


// here they are written in negation form for better composability
// Other controllers don't create Pod owned by a VSTS.
pub open spec fn interfere_create_pod_req(req: CreateRequest) -> StatePred<ClusterState> {
    let owner_references = req.obj.metadata.owner_references->0;
    &&& req.obj.metadata.owner_references is Some
    &&& exists |vsts: VStatefulSetView|
        #[trigger] owner_references.contains(vsts.controller_owner_ref())
}

// Other controllers don't create PVC matching VSTS's PVC template.
// this is stronger than storage_matches that we check pvc_template_name
// instead of pvc_template_name + existing a pod whose pvc matches requested obj
// Because even if there is no such pod running in cluster,
// PVC matching VSTS's template shouldn't be touched
pub open spec fn pvc_name_match(name: StringView, vsts: VStatefulSetView) -> bool {
    &&& exists |i: (PersistentVolumeClaimView, nat)| { // PVC, ordinal
        &&& #[trigger] vsts.spec.volume_claim_templates->0.contains(i.0)
        &&& name == Some(pvc_name(i.0.metadata.name->0, vsts.metadata.name->0, i.1))
    }
}

// create a PVC to be owned by a VSTS
pub open spec fn interfere_create_pvc_req(req: CreateRequest) -> bool {
    exists |vsts: VStatefulSetView| #[trigger] pvc_name_match(req.obj.metadata.name->0, vsts)
}

pub open spec fn interfere_update_pod_req(req: UpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        // request is valid
        &&& req.obj.metadata.resource_version is Some
        &&& {
            // Prevents 1): where other controllers update pod already owned
            // by a VSTS.
            ||| {
                let etcd_obj = s.resources()[req.key()];
                let owner_references = etcd_obj.metadata.owner_references->0;
                &&& s.resources().contains_key(req.key())
                &&& etcd_obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
                &&& etcd_obj.metadata.owner_references is Some
                &&& exists |vsts: VStatefulSetView|
                    #[trigger] owner_references.contains(vsts.controller_owner_ref())
            }
            // Prevents 2): where other controllers update pod so they become
            // owned by a VSTS.
            ||| (req.obj.metadata.owner_references is Some ==>
                    exists |vsts: VStatefulSetView| #[trigger] req.obj.metadata.owner_references->0.contains(vsts.controller_owner_ref()))
        }
    }
}

// It's simpler because name is included in object key and cannot be updated
// So we only the 1st case covering updates made by other controller to PVC owned by VSTS
pub open spec fn interfere_update_pvc_req(req: UpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        // request is valid
        &&& req.obj.metadata.resource_version is Some
        &&& exists |vsts: VStatefulSetView| #[trigger] pvc_name_match(req.name, vsts)
    }
}

// Other controllers don't try to delete pod owned by a VSTS.
pub open spec fn interfere_get_then_update_pod_req(req: GetThenUpdateRequest) -> bool {
    ||| {
        // Prevents 1): where other controllers update pod owned by a VSTS.
        // an object can has multiple owners, but only one controller owner
        // We force requests from other controllers to carry the controller owner reference
        // to achieve exclusive ownerships
        &&& req.owner_ref.controller is Some
        &&& req.owner_ref.controller->0
        &&& req.owner_ref.kind != VStatefulSetView::kind()
    }
    ||| {
        // Prevents 2): where other controllers update pods so they become owned by a VSTS.
        &&& req.obj.metadata.owner_references is Some
        &&& exists |vsts: VStatefulSetView| req.obj.metadata.owner_references->0.contains(#[trigger] vsts.controller_owner_ref()))
    }
}

// Other controllers don't try to delete pvc owned by a VSTS.
// because PVC owned by VSTS in etcd has no owner reference
// and the ownership check in handle_get_then_update_req will always fail
pub open spec fn interfere_get_then_update_pvc_req(req: GetThenUpdateRequest) -> bool {
    false
}

// No requirements on UpdateStatus Request
pub open spec fn interfere_update_pod_status_req(req: UpdateStatusRequest) -> bool {
    false
}

pub open spec fn interfere_update_pvc_status_req(req: UpdateStatusRequest) -> bool {
    false
}

// Other controllers don't try to delete a pod owned by a VSTS
pub open spec fn interfere_delete_pod_req(req: DeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& req.preconditions is Some
        &&& req.preconditions->0.resource_version is Some
        &&& {
            let etcd_obj = s.resources()[req.key];
            let owner_references = etcd_obj.metadata.owner_references->0;
            &&& s.resources().contains_key(req.key)
            &&& etcd_obj.metadata.resource_version is Some
            &&& etcd_obj.metadata.resource_version
                == req.preconditions->0.resource_version
            &&& etcd_obj.metadata.owner_references is Some
            &&& exists |vsts: VStatefulSetView| #[trigger] owner_references.contains(vsts.controller_owner_ref())
        }
    }
}

// Other controllers don't try to delete a pod matching a VSTS
pub open spec fn interfere_delete_pvc_req(req: DeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& req.preconditions is Some
        &&& req.preconditions->0.resource_version is Some
        &&& {
            let etcd_obj = s.resources()[req.key];
            let owner_references = etcd_obj.metadata.owner_references->0;
            &&& s.resources().contains_key(req.key)
            &&& etcd_obj.metadata.resource_version is Some
            &&& etcd_obj.metadata.resource_version
                == req.preconditions->0.resource_version
            &&& etcd_obj.metadata.name is Some
            &&& exists |vsts: VStatefulSetView| pvc_name_match(etcd_obj.metadata.name->0, vsts)
        }
    }
}

// Other controllers don't try to delete pod owned by a VSTS.
pub open spec fn interfere_get_then_delete_pod_req(req: GetThenDeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& req.owner_ref.controller is Some
        &&& req.owner_ref.controller->0
        &&& req.owner_ref.kind != VStatefulSetView::kind()
    }
}

// Other controllers don't try to delete pvc owned by a VSTS.
// because PVC owned by VSTS in etcd has no owner reference
// and the ownership check in handle_get_then_delete_req will always fail
pub open spec fn interfere_get_then_delete_pvc_req(req: GetThenDeleteRequest) -> bool {
    false
}

}