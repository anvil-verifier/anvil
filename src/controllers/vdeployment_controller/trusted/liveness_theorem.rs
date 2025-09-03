use crate::kubernetes_api_objects::spec::{prelude::*, pod_template_spec::*};
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
// Also try using quantifiers to simplify the proofs
pub open spec fn current_state_matches(vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let filtered_vrs_list = filter_vrs_managed_by_vd(vd, s.resources());
        &&& exists |new_vrs: VReplicaSetView| {
            // owned by vd, match template and has desired replicas
            &&& #[trigger] filtered_vrs_list.contains(new_vrs)
            &&& new_vrs_filter(vd.spec.template)(new_vrs)
            &&& new_vrs.spec.replicas.unwrap_or(int1!()) == vd.spec.replicas.unwrap_or(int1!())
            // all old vrs have 0 replicas
            &&& new_vrs.metadata.uid is Some
            &&& filtered_vrs_list.filter(old_vrs_filter(new_vrs.metadata.uid)).len() == 0
        }
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
pub open spec fn old_vrs_filter(new_vrs_uid: Option<Uid>) -> spec_fn(VReplicaSetView) -> bool {
    |vrs: VReplicaSetView| {
        &&& new_vrs_uid is None || vrs.metadata.uid->0 != new_vrs_uid->0
        &&& vrs.spec.replicas.unwrap_or(1) > 0
    }
}

pub open spec fn filter_vrs_managed_by_vd(vd: VDeploymentView, resources: StoredState) -> Seq<VReplicaSetView> {
    let objs = resources.values().filter(list_vrs_filter(vd.metadata.namespace->0)).to_seq();
    // simulate controller AfterListVRS step
    objects_to_vrs_list(objs).unwrap().filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd))
}

pub open spec fn dyn_objs_managed_by_vd(vd: VDeploymentView, s: ClusterState) -> Set<DynamicObjectView> {
    s.resources().values().filter(|o: DynamicObjectView| {
        &&& o.kind = VReplicaSetView
        &&& VReplicaSetView::unmarshal(o) is Ok
        &&& valid_owned_vrs(VReplicaSetView::unmarshal(o)->Ok_0, vd)
    })
}

}