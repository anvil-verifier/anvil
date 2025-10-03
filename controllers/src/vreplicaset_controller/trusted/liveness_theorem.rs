use verifiable_controllers::kubernetes_api_objects::spec::prelude::*;
use verifiable_controllers::kubernetes_cluster::spec::cluster::*;
use verifiable_controllers::temporal_logic::defs::*;
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
    |s: ClusterState|
        matching_pods(vrs, s.resources()).len() == vrs.spec.replicas.unwrap_or(0)
}

pub open spec fn matching_pods(vrs: VReplicaSetView, resources: StoredState) -> Set<DynamicObjectView> {
    resources.values().filter(|obj: DynamicObjectView| owned_selector_match_is(vrs, obj))
}

pub open spec fn owned_selector_match_is(vrs: VReplicaSetView, obj: DynamicObjectView) -> bool {
    &&& obj.kind == PodView::kind()
    &&& obj.metadata.namespace is Some
    &&& obj.metadata.namespace == vrs.metadata.namespace
    &&& obj.metadata.owner_references_contains(vrs.controller_owner_ref())
    &&& vrs.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
    &&& obj.metadata.deletion_timestamp is None
}

}
