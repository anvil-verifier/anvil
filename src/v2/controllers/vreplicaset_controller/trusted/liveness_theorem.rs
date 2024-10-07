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

// TODO: the current not_interfered_by invariant is radically strong. Weaken it later.
pub open spec fn vrs_not_interfered_by(other_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content.is_APIRequest()
            &&& msg.src == HostId::Controller(other_id)
        } ==> match msg.content.get_APIRequest_0() {
            APIRequest::CreateRequest(req) => req.obj.kind != Kind::PodKind,
            APIRequest::UpdateRequest(req) => req.obj.kind != Kind::PodKind,
            APIRequest::UpdateStatusRequest(req) => req.obj.kind != Kind::PodKind,
            APIRequest::DeleteRequest(req) => req.key.kind != Kind::PodKind,
            _ => true,
        }
    }
}

}
