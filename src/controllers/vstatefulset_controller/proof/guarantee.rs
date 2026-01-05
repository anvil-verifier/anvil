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

// VSTS Guarantee Condition (for other controllers)

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
        &&& req.obj.metadata.owner_references is Some
        &&& exists |vsts: VStatefulSetView| #[trigger]
            owner_references.contains(vsts.controller_owner_ref())
    }
    &&& req.obj.kind == PersistentVolumeClaimView::kind() ==> exists |vsts: VStatefulSetView|
        #[trigger] pvc_name_match(req.obj.metadata.name->0, vsts.metadata.name->0)
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

// VSTS internal Rely-Guarantee condition (for itself and used in shield lemma)

// all requests sent from one reconciliation do not interfere with other reconciliations on different CRs.
pub open spec fn no_interfering_request_between_vsts(controller_id: int, vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg) 
            &&& msg.content is APIRequest
            &&& msg.src == HostId::Controller(controller_id, vsts.object_ref())
        } ==> match msg.content->APIRequest_0 {
            APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true, // read-only requests
            APIRequest::CreateRequest(req) => {
                &&& req.namespace == vsts.object_ref().namespace
                &&& req.obj.metadata.name is Some
                &&& req.obj.kind == Kind::PodKind ==> {
                    &&& req.obj.metadata.owner_references == Some(Seq::empty().push(vsts.controller_owner_ref()))
                    &&& exists |ord: nat| req.key().name == #[trigger] pod_name(vsts.object_ref().name, ord)
                }
                &&& req.obj.kind == Kind::PersistentVolumeClaimKind ==> pvc_name_match(req.obj.metadata.name->0, vsts.metadata.name->0)
            },
            APIRequest::GetThenDeleteRequest(req) => {
                &&& req.key().namespace == vsts.object_ref().namespace
                &&& req.key().kind == Kind::PodKind
                &&& exists |ord: nat| req.key().name == #[trigger] pod_name(vsts.object_ref().name, ord)
                &&& req.owner_ref == vsts.controller_owner_ref()
            },
            APIRequest::GetThenUpdateRequest(req) => {
                &&& req.namespace == vsts.object_ref().namespace
                &&& req.obj.kind == Kind::PodKind
                &&& exists |ord: nat| req.name == #[trigger] pod_name(vsts.object_ref().name, ord)
                &&& req.owner_ref == vsts.controller_owner_ref()
                &&& req.obj.metadata.owner_references == Some(seq![vsts.controller_owner_ref()])
            },
            // VSTS controller will not issue DeleteRequest, UpdateRequest and UpdateStatusRequest
            _ => false
        }
    }
}

}