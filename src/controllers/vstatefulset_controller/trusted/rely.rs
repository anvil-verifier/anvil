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

pub open spec fn vsts_rely_conditions(cluster: Cluster, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |other_id: int| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] vsts_rely(other_id, cluster.installed_types)(s)
    }
}

pub open spec fn vsts_rely(other_id: int, installed_types: InstalledTypes) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(other_id)
        } ==> {
            let resp_msg = transition_by_etcd(installed_types, msg, s.api_server).1;
            ({ // either the request fails and etcd is not changed
                &&& resp_msg.content is APIResponse
                &&& is_ok_resp(resp_msg.content->APIResponse_0)
            }) ==> match (msg.content->APIRequest_0) { // or it does not mess up VSTS's objects
                APIRequest::CreateRequest(req) => rely_create_req(req),
                APIRequest::UpdateRequest(req) => rely_update_req(req)(s),
                APIRequest::GetThenUpdateRequest(req) => rely_get_then_update_req(req),
                APIRequest::DeleteRequest(req) => rely_delete_req(req)(s),
                APIRequest::GetThenDeleteRequest(req) => rely_get_then_delete_req(req),
                // Get/List requests do not interfere
                _ => true,
            }
        }
    }
}

pub open spec fn rely_create_req(req: CreateRequest) -> bool {
    match req.obj.kind {
        Kind::PodKind => rely_create_pod_req(req),
        Kind::PersistentVolumeClaimKind => rely_create_pvc_req(req),
        _ => true,
    }
}

// Other controllers don't create Pod owned by a VSTS.
// and should not create Pods with prefix of "vstatefulset-"
pub open spec fn rely_create_pod_req(req: CreateRequest) -> bool {
    // Prevents 1): where other controllers create pod owned by VSTS
    &&& !exists |vsts: VStatefulSetView| #[trigger] req.obj.metadata.owner_references_contains(vsts.controller_owner_ref())
    // Prevents 2): where other controllers create pod with name collision potential
    &&& !{
        if req.obj.metadata.name is Some {
            has_vsts_prefix(req.obj.metadata.name->0)
        } else {
            &&& req.obj.metadata.generate_name is Some
            &&& has_vsts_prefix(req.obj.metadata.generate_name->0)
        }
    }
}

// Other controllers don't create a PVC with name matching VSTS's naming convention
pub open spec fn rely_create_pvc_req(req: CreateRequest) -> bool {
    // does not have "vstatefulset-" prefix
    if req.obj.metadata.name is Some {
        !has_vsts_prefix(req.obj.metadata.name->0)
    } else {
        &&& req.obj.metadata.generate_name is Some
        &&& !has_vsts_prefix(req.obj.metadata.generate_name->0)
    }
}

pub open spec fn rely_update_req(req: UpdateRequest) -> StatePred<ClusterState> {
    match req.obj.kind {
        Kind::PodKind => rely_update_pod_req(req),
        Kind::PersistentVolumeClaimKind => |s: ClusterState| rely_update_pvc_req(req),
        _ => |s: ClusterState| true,
    }
}

// Other controllers don't try to update pod owned by a VSTS
pub open spec fn rely_update_pod_req(req: UpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        // does not interfere with VSTS-owned pods
        // Prevents 1): where other controllers update pod already owned by a VSTS.
        &&& !{
            let etcd_obj = s.resources()[req.key()];
            &&& exists |vsts: VStatefulSetView|
                #[trigger] etcd_obj.metadata.owner_references_contains(vsts.controller_owner_ref())
        }
        // Prevents 2): where other controllers update pod so they become owned by a VSTS.
        &&& !exists |vsts: VStatefulSetView| #[trigger] req.obj.metadata.owner_references_contains(vsts.controller_owner_ref())
    }
}

// Other controllers don't try to update PVC matching VSTS's PVC template.
pub open spec fn rely_update_pvc_req(req: UpdateRequest) -> bool {
    !exists |vsts: VStatefulSetView| #[trigger] pvc_name_match(req.name, vsts.metadata.name->0)
}

pub open spec fn rely_get_then_update_req(req: GetThenUpdateRequest) -> bool {
    match req.obj.kind {
        Kind::PodKind => rely_get_then_update_pod_req(req),
        Kind::PersistentVolumeClaimKind => rely_get_then_update_pvc_req(req),
        _ => true,
    }
}

// Other controllers don't try to delete pod owned by a VSTS.
pub open spec fn rely_get_then_update_pod_req(req: GetThenUpdateRequest) -> bool {
    // Prevents 1): where other controllers update pod owned by a VSTS.
    // an object can has multiple owners, but only one controller owner
    // We force requests from other controllers to carry the controller owner reference
    // to achieve exclusive ownerships
    &&& req.owner_ref.kind != VStatefulSetView::kind()
    // Prevents 2): where other controllers update pods so they become owned by a VSTS.
    &&& !exists |vsts: VStatefulSetView| #[trigger] req.obj.metadata.owner_references_contains(vsts.controller_owner_ref())
}

// Other controllers don't try to remove owner_references of a VSTS-owned PVC
pub open spec fn rely_get_then_update_pvc_req(req: GetThenUpdateRequest) -> bool {
    req.obj.metadata.owner_references is Some
    // if they try to update it, the request would fail because PVC has no owner reference
}

pub open spec fn rely_delete_req(req: DeleteRequest) -> StatePred<ClusterState> {
    match req.key.kind {
        Kind::PodKind => rely_delete_pod_req(req),
        Kind::PersistentVolumeClaimKind => |s: ClusterState| rely_delete_pvc_req(req),
        _ => |s: ClusterState| true,
    }
}

// Other controllers don't try to delete a pod owned by a VSTS
pub open spec fn rely_delete_pod_req(req: DeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        // that object does not belong to any VSTS
        !{
            let etcd_obj = s.resources()[req.key];
            &&& exists |vsts: VStatefulSetView| #[trigger] etcd_obj.metadata.owner_references_contains(vsts.controller_owner_ref())
        }
    }
}

// Other controllers don't try to delete a pod matching a VSTS
pub open spec fn rely_delete_pvc_req(req: DeleteRequest) -> bool {
    // that object does not match any VSTS PVC template
    !exists |vsts: VStatefulSetView| #[trigger] pvc_name_match(req.key().name, vsts.metadata.name->0)
}

pub open spec fn rely_get_then_delete_req(req: GetThenDeleteRequest) -> bool {
    match req.key.kind {
        Kind::PodKind => rely_get_then_delete_pod_req(req),
        _ => true, // GetThenDelete on PVC will fail because PVC owned by VSTS in etcd has no owner reference
    }
}

// Other controllers don't try to delete pod owned by a VSTS.
pub open spec fn rely_get_then_delete_pod_req(req: GetThenDeleteRequest) -> bool {
    // forbids get then delete on pod owned by a VSTS
    &&& req.owner_ref.kind != VStatefulSetView::kind()
}

// rely conditions for builtin controllers (only GC is supported now)
pub open spec fn garbage_collector_does_not_delete_vsts_pod_objects(vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src is BuiltinController
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
        } ==> {
            let req = msg.content.get_delete_request(); 
            &&& msg.content.is_delete_request()
            // &&& req.preconditions is Some
            // &&& req.preconditions.unwrap().uid is Some
            // &&& req.preconditions.unwrap().uid.unwrap() < s.api_server.uid_counter
            &&& s.resources().contains_key(req.key) ==> {
                let obj = s.resources()[req.key];
                &&& !(obj.metadata.owner_references_contains(vsts.controller_owner_ref())
                    && obj.kind == Kind::PodKind
                    && obj.metadata.namespace == vsts.metadata.namespace)
                // ||| obj.metadata.uid.unwrap() > req.preconditions.unwrap().uid.unwrap()
                &&& !(obj.kind == Kind::PersistentVolumeClaimKind
                    && obj.metadata.namespace == vsts.metadata.namespace
                    && obj.metadata.owner_references is None)
                    // && pvc_name_match(obj.metadata.name->0, vsts.metadata.name->0)
            }
        }
    }
}

}