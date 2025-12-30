use crate::kubernetes_api_objects::spec::{prelude::*, persistent_volume_claim::*};
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::kubernetes_cluster::spec::api_server::state_machine::*;
use crate::vstatefulset_controller::{
    trusted::spec_types::*,
    model::reconciler::*,
    proof::predicate::*
};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
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
            // they are written in negation form for better composability
            APIRequest::CreateRequest(req) => rely_create_req(req),
            APIRequest::UpdateRequest(req) => rely_update_req(req)(s),
            APIRequest::GetThenUpdateRequest(req) => rely_get_then_update_req(req),
            APIRequest::DeleteRequest(req) => rely_delete_req(req)(s),
            APIRequest::GetThenDeleteRequest(req) => rely_get_then_delete_req(req),
            // UpdateStatus and Get/List requests do not interfere
            _ => true,
        }
    }
}

pub open spec fn has_vsts_prefix(name: StringView) -> bool {
    exists |suffix| name == VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + suffix
}

pub open spec fn rely_create_req(req: CreateRequest) -> bool {
    match req.obj.kind {
        Kind::PodKind => !interfere_create_pod_req(req),
        Kind::PersistentVolumeClaimKind => !interfere_create_pvc_req(req),
        _ => true,
    }
}

// Other controllers don't create Pod owned by a VSTS.
// and should not create Pods with prefix of "vstatefulset-"
pub open spec fn interfere_create_pod_req(req: CreateRequest) -> bool {
    ||| {
        let owner_references = req.obj.metadata.owner_references->0;
        &&& req.obj.metadata.owner_references is Some
        &&& exists |vsts: VStatefulSetView| {
            &&& #[trigger] owner_references.contains(vsts.controller_owner_ref())
        }
    }
    ||| if req.obj.metadata.name is Some {
        has_vsts_prefix(req.obj.metadata.name->0)
    } else {
        &&& req.obj.metadata.generate_name is Some
        &&& has_vsts_prefix(req.obj.metadata.generate_name->0)
    }
}

// Other controllers don't create PVC matching VSTS's PVC template.
// this is stronger than storage_matches that we check pvc_template_name
// instead of pvc_template_name + existing a pod whose pvc matches requested obj
// Because even if there is no such pod running in cluster,
// PVC matching VSTS's template shouldn't be touched
pub open spec fn pvc_name_match(name: StringView, vsts: VStatefulSetView) -> bool {
    exists |i: (StringView, nat)| name == #[trigger] pvc_name(i.0, vsts.metadata.name->0, i.1)
}

// create a PVC with name matching VSTS's naming convention
pub open spec fn interfere_create_pvc_req(req: CreateRequest) -> bool {
    exists |vsts: VStatefulSetView| #[trigger] pvc_name_match(req.obj.metadata.name->0, vsts)
}

pub open spec fn rely_update_req(req: UpdateRequest) -> StatePred<ClusterState> {
    match req.obj.kind {
        Kind::PodKind => not!(interfere_update_pod_req(req)),
        Kind::PersistentVolumeClaimKind => not!(interfere_update_pvc_req(req)),
        _ => |s: ClusterState| true,
    }
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

pub open spec fn rely_get_then_update_req(req: GetThenUpdateRequest) -> bool {
    match req.obj.kind {
        Kind::PodKind => rely_get_then_update_pod_req(req),
        _ => true, // GetThenUpdate on PVC will fail because PVC owned by VSTS in etcd has no owner reference
    }
    
}

// Other controllers don't try to delete pod owned by a VSTS.
pub open spec fn rely_get_then_update_pod_req(req: GetThenUpdateRequest) -> bool {
    &&& {
        // Prevents 1): where other controllers update pod owned by a VSTS.
        // an object can has multiple owners, but only one controller owner
        // We force requests from other controllers to carry the controller owner reference
        // to achieve exclusive ownerships
        &&& req.owner_ref.controller is Some
        &&& req.owner_ref.controller->0
        &&& req.owner_ref.kind != VStatefulSetView::kind()
    }
    &&& !{
        // Prevents 2): where other controllers update pods so they become owned by a VSTS.
        &&& req.obj.metadata.owner_references is Some
        &&& exists |vsts: VStatefulSetView| req.obj.metadata.owner_references->0.contains(#[trigger] vsts.controller_owner_ref())
    }
}

pub open spec fn rely_delete_req(req: DeleteRequest) -> StatePred<ClusterState> {
    match req.key.kind {
        Kind::PodKind =>rely_delete_pod_req(req),
        Kind::PersistentVolumeClaimKind => not!(interfere_delete_pvc_req(req)),
        _ => |s: ClusterState| true,
    }
}

// Other controllers don't try to delete a pod owned by a VSTS
pub open spec fn rely_delete_pod_req(req: DeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let etcd_obj = s.resources()[req.key];
        // either the object does not exist
        ||| !s.resources().contains_key(req.key)
        // or tried to delete with stale rv
        ||| {
            &&& req.preconditions is Some
            &&& req.preconditions->0.resource_version is Some
            &&& etcd_obj.metadata.resource_version is Some
            &&& etcd_obj.metadata.resource_version
                != req.preconditions->0.resource_version
        }
        // or that object does not belong to any VSTS
        ||| {
            let owner_references = etcd_obj.metadata.owner_references->0;
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

pub open spec fn rely_get_then_delete_req(req: GetThenDeleteRequest) -> bool {
    match req.key.kind {
        Kind::PodKind => rely_get_then_delete_pod_req(req),
        _ => true, // GetThenDelete on PVC will fail because PVC owned by VSTS in etcd has no owner reference
    }
}

// Other controllers don't try to delete pod owned by a VSTS.
pub open spec fn rely_get_then_delete_pod_req(req: GetThenDeleteRequest) -> bool {
    &&& req.owner_ref.controller is Some
    &&& req.owner_ref.controller->0
    &&& req.owner_ref.kind != VStatefulSetView::kind()
}

// VSTS Guarantee Condition

pub open spec fn vsts_guarantee(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } ==> match msg.content->APIRequest_0 {
            APIRequest::CreateRequest(req) => vsts_guarantee_create_req(req),
            APIRequest::GetThenUpdateRequest(req) => vsts_guarantee_get_then_update_req(req),
            APIRequest::GetThenDeleteRequest(req) => vsts_guarantee_get_then_delete_req(req),
            // No Update, UpdateStatus and Delete requests submitted
            _ => true,
        }
    }
}

// VSTS controller only creates Pods owned by itself
// and only creates PVC matching its PVC templates
pub open spec fn vsts_guarantee_create_req(req: CreateRequest) -> bool {
    let owner_references = req.obj.metadata.owner_references->0;
    &&& req.obj.kind == PodView::kind() ==> {
        &&& req.obj.metadata.name is Some
        &&& has_vsts_prefix(req.obj.metadata.name->0)
        &&& exists |vsts: VStatefulSetView| #[trigger]
            owner_references.contains(vsts.controller_owner_ref())
    }
    &&& req.obj.kind == PersistentVolumeClaimView::kind() ==> exists |vsts: VStatefulSetView|
        #[trigger] pvc_name_match(req.obj.metadata.name->0, vsts)
}

// VSTS controller Only updates Pod owned by itself and does not update PVC
pub open spec fn vsts_guarantee_get_then_update_req(req: GetThenUpdateRequest) -> bool {
    &&& req.obj.kind == PodView::kind()
    &&& has_vsts_prefix(req.obj.metadata.name->0)
    &&& exists |vsts: VStatefulSetView| {
        &&& req.owner_ref == #[trigger] vsts.controller_owner_ref()
        // do not change ownership
        &&& req.obj.metadata.owner_references_contains(vsts.controller_owner_ref())
    }
}

// VSTS controller Only deletes Pod owned by itself
pub open spec fn vsts_guarantee_get_then_delete_req(req: GetThenDeleteRequest) -> bool {
    &&& req.key.kind == PodView::kind()
    &&& exists |vsts: VStatefulSetView| req.owner_ref == #[trigger] vsts.controller_owner_ref()
}

}