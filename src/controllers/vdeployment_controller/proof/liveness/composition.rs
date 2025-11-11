use crate::kubernetes_cluster::proof::composition::*;
use crate::temporal_logic::defs::*;
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::trusted::{
    spec_types::*, liveness_theorem::*, rely_guarantee::*
};
use crate::vdeployment_controller::model::{
    reconciler::*, install::*
};
use crate::vdeployment_controller::proof::{
    guarantee::*
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus !{


impl Composition for VDeploymentReconciler {
    open spec fn c() -> ControllerSpec {
        liveness_guarantee: true_pred(),
        liveness_rely: true_pred(),
        safety_guarantee: always(lift_state(vd_guarantee(controller_id))),
        safety_partial_rely: |other_id: int| lift_state(vd_rely(other_id)),
        fairness: |i: int| true_pred(),
        membership: |cluster: Cluster, id: int| cluster.controller_models.contains_pair(id, vd_controller_model()),
    }

    uninterp spec fn id() -> int;

    uninterp spec fn composed() -> Map<int, ControllerSpec>;

    proof fn safety_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster)
    requires
        (Self::c().membership)(cluster, Self::id()),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    ensures
        spec.entails(Self::c().safety_guarantee),
    {
        guarantee_condition_holds(spec, cluster, Self::id());
    }
}


}