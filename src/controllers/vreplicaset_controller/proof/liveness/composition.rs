use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::vdeployment_controller::trusted::spec_types::*;
use crate::vreplicaset_controller::trusted::{
    spec_types::*, rely_guarantee::*, liveness_theorem::*
};
use crate::vreplicaset_controller::model::{
    reconciler::*, install::*
};
use crate::vreplicaset_controller::proof::{
    guarantee::*
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus !{


impl Composition for VReplicaSetReconciler {
    open spec fn c() -> ControllerSpec {
        ControllerSpec{
            liveness_guarantee: tla_forall(|vrs: VReplicaSetView| always(lift_state(current_state_matches(vrs)))),
            liveness_rely: true_pred(), // VRS does not require assumptions of other controller's ESR
            safety_guarantee: always(lift_state(vrs_guarantee(Self::id()))),
            safety_partial_rely: |other_id: int| lift_state(vrs_rely(other_id)),
            fairness: |i: int| true_pred(),
            membership: |cluster: Cluster, id: int| cluster.controller_models.contains_pair(id, vrs_controller_model()),
        }
    }

    uninterp spec fn id() -> int;

    // Q: should we add VD controller here
    closed spec fn composed() -> Map<int, ControllerSpec> {
        Map::empty().insert(Self::id(), Self::c())
    }

    proof fn safety_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster)
    ensures
        spec.entails(Self::c().safety_guarantee),
    {
        guarantee_condition_holds(spec, cluster, Self::id());
    }

    proof fn no_internal_interference(spec: TempPred<ClusterState>, cluster: Cluster)
    ensures
        forall |i| #[trigger] Self::composed().contains_key(i) ==>
            spec.entails((Self::c().safety_partial_rely)(i))
            && spec.entails((Self::composed()[i].safety_partial_rely)(Self::id()))
    {}
}


}