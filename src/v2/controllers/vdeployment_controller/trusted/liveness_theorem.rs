use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::trusted::{spec_types::*, util::*};
use crate::vreplicaset_controller::trusted::liveness_theorem::*;
use vstd::prelude::*;

verus !{

// draft of ESR for VDeployment
// TODO: add another version which talks about pods and derives from VRS ESR and this ESR
pub open spec fn current_state_matches(vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let dyn_vrs_list = s.resources().values().to_seq().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind());
        let vrs_list = objects_to_vrs_list(dyn_vrs_list);
        let filtered_vrs_list = filter_vrs_list(vrs_list.unwrap(), vd);
        let (new_vrs_list, old_vrs_list) = filter_old_and_new_vrs(filtered_vrs_list, vd);
        &&& vrs_list.is_Some()
        &&& new_vrs_list.len() == 1
        &&& old_vrs_list.len() == 0
        &&& new_vrs_list[0].spec.replicas.unwrap_or(1) == vd.spec.replicas.unwrap_or(1)
        &&& match_template_without_hash(vd, new_vrs_list[0])
        //&&& current_state_matches(new_vrs_list[0])
    }
}

}