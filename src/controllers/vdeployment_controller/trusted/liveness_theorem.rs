use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::trusted::{spec_types::*, util::*};
use crate::vreplicaset_controller::trusted::liveness_theorem::*;
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
        let objs = s.resources().values().filter(|obj: DynamicObjectView| {
            &&& obj.kind == VReplicaSetView::kind()
            &&& obj.metadata.namespace == vd.metadata.namespace
        }).to_seq();
        let vrs_list = objects_to_vrs_list(objs);
        let filtered_vrs_list = filter_vrs_list(vd, vrs_list.unwrap());
        let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(vd, filtered_vrs_list);
        &&& vrs_list.is_Some()
        &&& old_vrs_list.len() == 0
        &&& new_vrs.is_Some()
        &&& new_vrs.unwrap().spec.replicas.unwrap_or(1) == vd.spec.replicas.unwrap_or(1)
        &&& match_template_without_hash(vd, new_vrs.get_Some_0())
        //&&& current_state_matches(new_vrs_list[0])
    }
}

}