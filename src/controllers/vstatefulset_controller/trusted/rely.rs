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
            APIRequest::CreateRequest(req) => rely_create_req(req),
            APIRequest::UpdateRequest(req) => rely_update_req(req),
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
            APIRequest::CreateRequest(req) => rely_create_req(req),
            APIRequest::UpdateRequest(req) => rely_update_req(req),
            APIRequest::GetThenUpdateRequest(req) => rely_get_then_update_req(req),
            APIRequest::DeleteRequest(req) => rely_delete_req(req),
            APIRequest::GetThenDeleteRequest(req) => rely_get_then_delete_req(req),
            // Get/List/UpdateStatus requests are unconstrained
            _ => true,
        }
    }
}

pub open spec fn rely_create_req(req: CreateRequest) -> bool {
    match req.obj.kind {
        Kind::PodKind | Kind::PersistentVolumeClaimKind => !{
            if req.obj.metadata.name is Some {
                has_vsts_prefix(req.obj.metadata.name->0)
            } else {
                &&& req.obj.metadata.generate_name is Some
                &&& has_vsts_prefix(req.obj.metadata.generate_name->0)
            }
        },
        _ => true,
    }
}

pub open spec fn rely_update_req(req: UpdateRequest) -> bool {
    match req.obj.kind {
        Kind::PodKind | Kind::PersistentVolumeClaimKind => !has_vsts_prefix(req.name),
        _ => true,
    }
}

pub open spec fn rely_get_then_update_req(req: GetThenUpdateRequest) -> bool {
    match req.obj.kind {
        Kind::PodKind | Kind::PersistentVolumeClaimKind => !has_vsts_prefix(req.name),
        _ => true,
    }
}

pub open spec fn rely_delete_req(req: DeleteRequest) -> bool {
    match req.key.kind {
        Kind::PodKind | Kind::PersistentVolumeClaimKind => !has_vsts_prefix(req.key.name),
        _ => true,
    }
}

// GetThenDelete on PVC will fail because PVC owned by VSTS in etcd has no owner reference
// but to simplify the proof, we still disallow GetThenDelete on PVC with vsts prefix
pub open spec fn rely_get_then_delete_req(req: GetThenDeleteRequest) -> bool {
    match req.key.kind {
        Kind::PodKind | Kind::PersistentVolumeClaimKind => !has_vsts_prefix(req.key.name),
        _ => true,
    }
}

}