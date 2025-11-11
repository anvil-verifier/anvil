use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::vreplicaset_controller::trusted::liveness_theorem as vrs_liveness;
use crate::vdeployment_controller::trusted::liveness_theorem as vd_liveness;
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vreplicaset_controller::model::reconciler::VReplicaSetReconciler;
// Q: we have to add some to pub_mod
use crate::vreplicaset_controller::proof::liveness::composition::*;
use crate::vdeployment_controller::trusted::{
    spec_types::*, rely_guarantee::*
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
        ControllerSpec{
            // Q: tla_forall?
            liveness_guarantee: tla_forall(|vd: VDeploymentView| always(lift_state(vd_liveness::current_state_matches(vd)))),
            liveness_rely: tla_forall(|vrs: VReplicaSetView| always(lift_state(vrs_liveness::current_state_matches(vrs)))),
            safety_guarantee: always(lift_state(vd_guarantee(Self::id()))),
            safety_partial_rely: |other_id: int| lift_state(vd_rely(other_id)),
            fairness: |i: int| true_pred(), // Q: what should be included
            membership: |cluster: Cluster, id: int| {
                &&& cluster.controller_models.contains_pair(id, vd_controller_model())
                // Q: should they be included here
                &&& cluster.type_is_installed_in_cluster::<VDeploymentView>()
                &&& cluster.type_is_installed_in_cluster::<VReplicaSetView>()
            },
        }
    }

    uninterp spec fn id() -> int;

    // Q: do we need this
    // #[verifier(external_body)]
    // pub proof fn id_is_unique()
    // ensures
    //     Self::id() != VReplicaSetReconciler::id(),
    // ;

    closed spec fn composed() -> Map<int, ControllerSpec> {
        Map::<int, ControllerSpec>::empty()
            .insert(Self::id(), Self::c())
            .insert(VReplicaSetReconciler::id(), VReplicaSetReconciler::c())
    }

    // Q: error: trait method implementation cannot declare requires clauses; these can only be inherited from the trait declaration
    // post is allowed?
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