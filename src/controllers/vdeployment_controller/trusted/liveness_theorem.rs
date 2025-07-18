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
        // make it consistent with API server's handle_list_req
        let objs = s.resources().values().filter(list_vrs_obj_filter(vd)).to_seq();
        let (new_vrs, old_vrs_list) = filter_old_and_new_vrs_on_etcd(vd, s.resources());
        // this step may return None so we need to check here
        &&& objects_to_vrs_list(objs) is Some
        &&& old_vrs_list.len() == 0
        // TODO: add requirements on owner_ref
        &&& new_vrs is Some
        &&& match_template_without_hash(vd, new_vrs->0)
        &&& match_replicas(vd, new_vrs->0)
        //&&& current_state_matches(new_vrs_list[0])
    }
}

pub open spec fn filter_old_and_new_vrs_on_etcd(vd: VDeploymentView, resources: StoredState) -> (Option<VReplicaSetView>, Seq<VReplicaSetView>) {
    let objs = resources.values().filter(list_vrs_obj_filter(vd)).to_seq();
    let filtered_vrs_list = objects_to_vrs_list(objs).unwrap().filter(|vrs: VReplicaSetView| valid_owned_object(vrs, vd));
    filter_old_and_new_vrs(vd, filtered_vrs_list)
}

pub open spec fn list_vrs_obj_filter(vd: VDeploymentView) -> spec_fn(DynamicObjectView) -> bool {
    |obj: DynamicObjectView| {
        &&& obj.kind == VReplicaSetView::kind()
        &&& obj.metadata.namespace == vd.metadata.namespace
    }
}

}