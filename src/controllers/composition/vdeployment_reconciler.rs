use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::vreplicaset_controller::trusted::liveness_theorem as vrs_liveness;
use crate::vdeployment_controller::trusted::liveness_theorem as vd_liveness;
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vreplicaset_controller::model::reconciler::VReplicaSetReconciler;
use crate::composition::vreplicaset_reconciler::*;
use crate::vdeployment_controller::trusted::{
    spec_types::*, rely_guarantee::*
};
use crate::vdeployment_controller::model::{
    reconciler::*, install::*
};
use crate::vdeployment_controller::proof::{
    guarantee::*, liveness::{spec::*, proof::*}
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus !{


impl Composition for VDeploymentReconciler {
    open spec fn c() -> ControllerSpec {
        ControllerSpec{
            liveness_guarantee: tla_forall(|vd: VDeploymentView| always(lift_state(vd_liveness::desired_state_is(vd)).leads_to(always(lift_state(vd_liveness::current_pods_matches(vd)))))),
            liveness_rely: tla_forall(|vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs)).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))))),
            safety_guarantee: always(lift_state(vd_guarantee(Self::id()))),
            safety_partial_rely: |other_id: int| lift_state(vd_rely(other_id)),
            fairness: |cluster: Cluster| next_with_wf(cluster, Self::id()).and(next_with_wf(cluster, VReplicaSetReconciler::id())),
            membership: |cluster: Cluster, id: int| {
                &&& cluster.controller_models.contains_pair(id, vd_controller_model())
                &&& cluster.type_is_installed_in_cluster::<VDeploymentView>()
                &&& cluster.type_is_installed_in_cluster::<VReplicaSetView>()
            },
        }
    }

    uninterp spec fn id() -> int;

    open spec fn composed() -> Map<int, ControllerSpec> {
        Map::<int, ControllerSpec>::empty().insert(VReplicaSetReconciler::id(), VReplicaSetReconciler::c())
    }

    // for trait proof implementation, requires conditions are already included here
    proof fn safety_guarantee_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().safety_guarantee),
    {
        guarantee_condition_holds(spec, cluster, Self::id());
    }

    #[verifier(external_body)]
    proof fn safety_rely_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures forall |i| #[trigger] Self::composed().contains_key(i) ==>
            spec.entails((Self::c().safety_partial_rely)(i))
            && spec.entails((Self::composed()[i].safety_partial_rely)(Self::id()))
    {}
}

impl VerticalComposition for VDeploymentReconciler {
    #[verifier(external_body)]
    proof fn liveness_guarantee_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().liveness_guarantee),
    {
        eventually_stable_reconciliation_holds(spec, cluster, Self::id());
    }

    proof fn liveness_rely_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().liveness_rely),
    {
        assert(Self::composed().contains_key(VReplicaSetReconciler::id())); // trigger
    }
}

proof fn eventually_stable_reconciliation_holds_for_vd_and_vrs()
{}


}