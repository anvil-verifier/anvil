use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::trusted::{spec_types::*, util::*};
use crate::vreplicaset_controller::trusted::liveness_theorem::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus !{

pub open spec fn vd_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation(|vd| current_state_matches(vd))
}

pub open spec fn vd_eventually_stable_reconciliation_per_cr(vd: VDeploymentView) -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation_per_cr(vd, |vd| current_state_matches(vd))
}

// draft of ESR for VDeployment
// TODO: add another version which talks about pods and derives from VRS ESR and this ESR
pub open spec fn current_state_matches(vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let filtered_vrs_list = filter_vrs_managed_by_vd(vd, s.resources());
        let new_vrs_list = filtered_vrs_list.filter(new_vrs_filter(vd.spec.template));
        let old_vrs_list = filtered_vrs_list.filter(old_vrs_filter(new_vrs_list[0].metadata.uid));
        &&& new_vrs_list.filter(|vrs| vrs.spec.replicas.unwrap_or(1) > 0).len() == 1
        &&& new_vrs_list[0].metadata.uid is Some
        &&& match_replicas(vd, new_vrs_list[0])
        &&& old_vrs_list.len() == 0
    }
}

// simulate API server list filter
pub open spec fn list_vrs_filter(namespace: StringView) -> spec_fn(DynamicObjectView) -> bool {
    |o: DynamicObjectView| {
        &&& o.object_ref().namespace == namespace
        &&& o.object_ref().kind == VReplicaSetView::kind()
    }
}

pub open spec fn new_vrs_filter(template: PodTemplateSpecView) -> spec_fn(VReplicaSetView) -> bool {
    |vrs: VReplicaSetView| match_template_without_hash(template, vrs)
}

// None -> no new vrs
pub open spec fn old_vrs_filter(new_vrs: Option<VReplicaSetView>) -> spec_fn(VReplicaSetView) -> bool {
    |vrs: VReplicaSetView| {
        &&& new_vrs is None || vrs.metadata.uid != new_vrs.metadata.uid->0
        &&& vrs.spec.replicas.unwrap_or(1) > 0
    }
}

pub open spec fn filter_vrs_managed_by_vd(vd: VDeploymentView, resources: StoredState) -> Seq<VReplicaSetView> {
    let objs = resources.values().filter(list_vrs_filter(vd.metadata.namespace->0)).to_seq();
    // simulate controller AfterListVRS step
    objects_to_vrs_list(objs).unwrap().filter(|vrs: VReplicaSetView| valid_owned_object(vrs, vd))
}

}