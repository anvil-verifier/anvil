use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstatefulset_controller::{
    model::{install::*, reconciler::*},
    proof::predicate::*,
    trusted::{rely_guarantee::*, spec_types::*, liveness_theorem::*, step::VStatefulSetReconcileStepView::*},
};
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*, string_view::*};
use vstd::{seq_lib::*, map_lib::*, set_lib::*};
use vstd::prelude::*;

verus! {

// In addition to rely conditions, we also need to prove vsts controller's internal guarantee:
// all requests sent from one reconciliation do not interfere with other reconciliations on different CRs.
pub open spec fn no_interfering_request_between_vsts(vsts_key: ObjectRef, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let vsts = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[vsts_key].triggering_cr).unwrap();
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src == HostId::Controller(controller_id, vsts_key)
            &&& s.ongoing_reconciles(controller_id).contains_key(vsts_key)
        } ==> match msg.content->APIRequest_0 {
            APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true, // read-only requests
            APIRequest::CreateRequest(req) => {
                &&& req.obj.kind == PodView::kind() ==> {
                    // these 2 may not be necessary
                    // &&& req.namespace == vsts_key.namespace
                    // &&& req.obj.kind == PodView::kind()
                    &&& req.obj.metadata.owner_references == Some(Seq::empty().push(vsts.controller_owner_ref()))
                    &&& exists |ord: nat| req.obj.metadata.name == Some(#[trigger] pod_name(vsts_key.name, ord))
                }
                &&& req.obj.kind == PersistentVolumeClaimView::kind() ==> exists |i: (int, nat)| // PVC template index, ordinal
                    req.obj.metadata.name == Some(pvc_name(vsts.spec.volume_claim_templates->0[i.0].metadata.name->0, vsts_key.name, i.1))
            },
            APIRequest::GetThenDeleteRequest(req) => {
                &&& req.key().kind == PodView::kind()
                &&& req.owner_ref == vsts.controller_owner_ref()
            },
            APIRequest::GetThenUpdateRequest(req) => {
                &&& req.obj.kind == PodView::kind()
                &&& req.owner_ref == vsts.controller_owner_ref()
                &&& exists |ord: nat| req.name == #[trigger] pod_name(vsts_key.name, ord)
                &&& req.namespace == vsts_key.namespace
            },
            // VSTS controller will not issue DeleteRequest, UpdateRequest
            _ => true
        }
    }
}
    
}