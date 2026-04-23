use crate::kubernetes_api_objects::spec::{prelude::*, persistent_volume_claim::*};
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::kubernetes_cluster::spec::api_server::{state_machine::*, types::InstalledTypes};
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

pub open spec fn vsts_rely_conditions_pod_monkey() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src is PodMonkey
            &&& msg.content is APIRequest
        } ==> match (msg.content->APIRequest_0) {
            APIRequest::CreateRequest(req) => vsts_rely_create_req(req),
            APIRequest::UpdateRequest(req) => vsts_rely_update_req(req)(s),
            _ => true, // Deletion/UpdateStatus requests are allowed
        }
    }
}

// rely conditions for other controllers
pub open spec fn vsts_rely_conditions(cluster: Cluster, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |other_id: int| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] vsts_rely(other_id)(s)
    }
}

pub open spec fn vsts_rely(other_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(other_id)
        } ==> match (msg.content->APIRequest_0) {
            APIRequest::CreateRequest(req) => vsts_rely_create_req(req),
            APIRequest::UpdateRequest(req) => vsts_rely_update_req(req)(s),
            APIRequest::GetThenUpdateRequest(req) => vsts_rely_get_then_update_req(req),
            APIRequest::DeleteRequest(req) => vsts_rely_delete_req(req)(s),
            APIRequest::GetThenDeleteRequest(req) => vsts_rely_get_then_delete_req(req),
            // Get/List/UpdateStatus requests are unconstrained
            _ => true,
        }
    }
}

pub open spec fn vsts_rely_create_req(req: CreateRequest) -> bool {
    match req.obj.kind {
        Kind::PodKind | Kind::PersistentVolumeClaimKind => {
            // no name conflict
            &&& !if req.obj.metadata.name is Some {
                    has_vsts_prefix(req.obj.metadata.name->0)
                } else {
                    &&& req.obj.metadata.generate_name is Some
                    &&& has_vsts_prefix(req.obj.metadata.generate_name->0)
                }
            // no ownership interference
            &&& !exists |vsts: VStatefulSetView|
                #[trigger] req.obj.metadata.owner_references_contains(vsts.controller_owner_ref())
        },
        _ => true,
    }
}

// After we support orphan adoption, we need to talk about resource version
pub open spec fn vsts_rely_update_req(req: UpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        match req.obj.kind {
            Kind::PodKind | Kind::PersistentVolumeClaimKind => {
                &&& !has_vsts_prefix(req.name)
                // Prevents 1): where other controllers update pod already owned by a VSTS.
                &&& !exists |vsts: VStatefulSetView|
                    #[trigger] s.resources()[req.key()].metadata.owner_references_contains(vsts.controller_owner_ref())
                // Prevents 2): where other controllers update pod so they become owned by a VSTS.
                &&& !exists |vsts: VStatefulSetView| #[trigger] req.obj.metadata.owner_references_contains(vsts.controller_owner_ref()) 
            }
            _ => true,
        }
    }
}

pub open spec fn vsts_rely_get_then_update_req(req: GetThenUpdateRequest) -> bool {
    match req.obj.kind {
        Kind::PodKind | Kind::PersistentVolumeClaimKind => {
            &&& !has_vsts_prefix(req.name)
            // Prevents 1): where other controllers update pod already owned by a VSTS.
            &&& req.owner_ref.kind != VStatefulSetView::kind()
            // Prevents 2): where other controllers update pod so they become owned by a VSTS.
            &&& !exists |vsts: VStatefulSetView| #[trigger] req.obj.metadata.owner_references_contains(vsts.controller_owner_ref()) 
        }
        _ => true,
    }
}

pub open spec fn vsts_rely_delete_req(req: DeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        match req.key.kind {
            Kind::PodKind | Kind::PersistentVolumeClaimKind => {
                &&& !has_vsts_prefix(req.key.name)
                // Prevents 1): where other controllers delete pod already owned by a VSTS.
                &&& !exists |vsts: VStatefulSetView| #[trigger] s.resources()[req.key()].metadata.owner_references_contains(vsts.controller_owner_ref())
            }
            _ => true,
        }
    }
}

// GetThenDelete on PVC will fail because PVC owned by VSTS in etcd has no owner reference
// but to simplify the proof, we still disallow GetThenDelete on PVC with vsts prefix
pub open spec fn vsts_rely_get_then_delete_req(req: GetThenDeleteRequest) -> bool {
    match req.key.kind {
        Kind::PodKind | Kind::PersistentVolumeClaimKind => {
            &&& !has_vsts_prefix(req.key.name)
            // Prevents 1): where other controllers delete pod already owned by a VSTS.
            &&& req.owner_ref.kind != VStatefulSetView::kind()
        }
        _ => true,
    }
}

// VSTS Guarantee Condition (for other controllers)

pub open spec fn vsts_guarantee(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } ==> match msg.content->APIRequest_0 {
            APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true, // read-only requests
            APIRequest::CreateRequest(req) => vsts_guarantee_create_req(req),
            APIRequest::GetThenUpdateRequest(req) => vsts_guarantee_get_then_update_req(req),
            APIRequest::GetThenDeleteRequest(req) => vsts_guarantee_get_then_delete_req(req),
            // No Update, UpdateStatus and Delete requests submitted
            _ => false,
        }
    }
}

// VSTS controller only creates Pods owned by itself
// and only creates PVC matching its PVC templates
pub open spec fn vsts_guarantee_create_req(req: CreateRequest) -> bool {
    let owner_references = req.obj.metadata.owner_references->0;
    &&& req.obj.metadata.name is Some
    &&& has_vsts_prefix(req.obj.metadata.name->0)
    &&& (req.obj.kind == Kind::PodKind || req.obj.kind == Kind::PersistentVolumeClaimKind)
    &&& req.obj.kind == Kind::PodKind
        ==> exists |vsts: VStatefulSetView| req.obj.metadata.owner_references == Some(Seq::empty().push(#[trigger] vsts.controller_owner_ref()))
    &&& req.obj.kind == Kind::PersistentVolumeClaimKind
        ==> req.obj.metadata.owner_references is None
}

// VSTS controller Only updates Pod owned by itself and does not update PVC
pub open spec fn vsts_guarantee_get_then_update_req(req: GetThenUpdateRequest) -> bool {
    &&& req.obj.kind == Kind::PodKind
    &&& req.obj.metadata.name is Some
    &&& has_vsts_prefix(req.name)
    &&& exists |vsts: VStatefulSetView| {
        &&& req.owner_ref == #[trigger] vsts.controller_owner_ref()
        // do not change ownership
        &&& req.obj.metadata.owner_references == Some(Seq::empty().push(req.owner_ref))
    }
}

// VSTS controller Only deletes Pod owned by itself
pub open spec fn vsts_guarantee_get_then_delete_req(req: GetThenDeleteRequest) -> bool {
    &&& req.key.kind == Kind::PodKind
    &&& has_vsts_prefix(req.key.name)
    &&& exists |vsts: VStatefulSetView| req.owner_ref == #[trigger] vsts.controller_owner_ref()
}

}