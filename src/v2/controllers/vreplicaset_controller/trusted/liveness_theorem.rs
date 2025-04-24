use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::temporal_logic::defs::*;
use crate::vreplicaset_controller::trusted::spec_types::*;
use vstd::prelude::*;

verus! {

pub open spec fn vrs_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation(|vrs| current_state_matches(vrs))
}

pub open spec fn vrs_eventually_stable_reconciliation_per_cr(vrs: VReplicaSetView) -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation_per_cr(vrs, |vrs| current_state_matches(vrs))
}

pub open spec fn current_state_matches(vrs: VReplicaSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let pods: Set<ObjectRef> = Set::new(|key: ObjectRef| {
            &&& s.resources().contains_key(key)
            &&& owned_selector_match_is(vrs, s.resources()[key])
        });
        pods.len() == vrs.spec.replicas.unwrap_or(0)
    }
}

pub open spec fn owned_selector_match_is(vrs: VReplicaSetView, obj: DynamicObjectView) -> bool {
    &&& obj.kind == PodView::kind()
    &&& obj.metadata.namespace.is_Some()
    &&& obj.metadata.namespace == vrs.metadata.namespace
    &&& obj.metadata.owner_references_contains(vrs.controller_owner_ref())
    &&& vrs.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
    &&& obj.metadata.deletion_timestamp.is_None()
}

// Other controllers don't create pods owned by a VReplicaSet.
pub open spec fn vrs_not_interfered_by_create_req(req: CreateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == Kind::PodKind ==> !{
            let etcd_obj = s.resources()[req.key()];
            let owner_references = etcd_obj.metadata.owner_references.get_Some_0();
            &&& s.resources().contains_key(req.key())
            &&& etcd_obj.metadata.resource_version.is_Some()
            &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
            &&& etcd_obj.metadata.owner_references.is_Some()
            &&& exists |vrs: VReplicaSetView| 
                #[trigger] owner_references.contains(vrs.controller_owner_ref())
        }
    }
}

// Other controllers don't try to update pods owned by a VReplicaSet.
pub open spec fn vrs_not_interfered_by_update_req(req: UpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == Kind::PodKind ==> !{
            let etcd_obj = s.resources()[req.key()];
            let owner_references = etcd_obj.metadata.owner_references.get_Some_0();
            &&& s.resources().contains_key(req.key())
            &&& etcd_obj.metadata.resource_version.is_Some()
            &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
            &&& etcd_obj.metadata.owner_references.is_Some()
            &&& exists |vrs: VReplicaSetView| 
                #[trigger] owner_references.contains(vrs.controller_owner_ref())
        }
    }
}

// Dealt with similarly to update requests.
// TODO: allow other controllers to send UpdateStatus
// requests to owned pods after we address the fairness issues.
pub open spec fn vrs_not_interfered_by_update_status_req(req: UpdateStatusRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == Kind::PodKind ==> !{
            let etcd_obj = s.resources()[req.key()];
            let owner_references = etcd_obj.metadata.owner_references.get_Some_0();
            &&& s.resources().contains_key(req.key())
            &&& etcd_obj.metadata.resource_version.is_Some()
            &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
            &&& etcd_obj.metadata.owner_references.is_Some()
            &&& exists |vrs: VReplicaSetView| 
                #[trigger] owner_references.contains(vrs.controller_owner_ref())
        }
    }
}

// All delete requests carry a precondition on the resource version,
// and other controllers don't try to delete pods owned by a VReplicaSet.
pub open spec fn vrs_not_interfered_by_delete_req(req: DeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.key.kind == Kind::PodKind ==>
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

pub open spec fn vrs_not_interfered_by(other_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content.is_APIRequest()
            &&& msg.src == HostId::Controller(other_id)
        } ==> match msg.content.get_APIRequest_0() {
            APIRequest::CreateRequest(req) => vrs_not_interfered_by_create_req(req)(s),
            APIRequest::UpdateRequest(req) => vrs_not_interfered_by_update_req(req)(s),
            APIRequest::UpdateStatusRequest(req) => vrs_not_interfered_by_update_status_req(req)(s),
            APIRequest::DeleteRequest(req) => vrs_not_interfered_by_delete_req(req)(s),
            _ => true,
        }
    }
}
}
