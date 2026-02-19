use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::rabbitmq_controller::trusted::{
    spec_types::*, rely_guarantee::*, liveness_theorem::*
};
use crate::rabbitmq_controller::model::{
    reconciler::*, install::*
};
use crate::vstatefulset_controller::trusted::{
    spec_types::VStatefulSetView,
    liveness_theorem as vsts_liveness_theorem,
};
use crate::vstatefulset_controller::model::{
    reconciler::VStatefulSetReconciler, install::vsts_controller_model
};
use crate::vstatefulset_controller::proof::liveness::spec as vsts_spec;
use crate::composition::vstatefulset_controller;

use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus !{


impl Composition for RabbitmqReconciler {
    open spec fn c() -> ControllerSpec {
        ControllerSpec{
            liveness_guarantee: rmq_composed_eventually_stable_reconciliation(),
            liveness_rely: vsts_liveness_theorem::vsts_eventually_stable_reconciliation(),
            safety_guarantee: always(lift_state(rmq_guarantee(Self::id()))),
            safety_partial_rely: |other_id: int| always(lift_state(rmq_rely(other_id))),
            fairness: |cluster: Cluster| vsts_spec::next_with_wf(cluster, Self::id()),
            membership: |cluster: Cluster, id: int| {
                &&& cluster.controller_models.contains_pair(VStatefulSetReconciler::id(), vsts_controller_model())
                &&& cluster.controller_models.contains_pair(Self::id(), rabbitmq_controller_model())
                &&& cluster.type_is_installed_in_cluster::<RabbitmqClusterView>()
                &&& cluster.type_is_installed_in_cluster::<VStatefulSetView>()
            },
        }
    }

    uninterp spec fn id() -> int;

    open spec fn composed() -> Map<int, ControllerSpec> {
        Map::<int, ControllerSpec>::empty().insert(VStatefulSetReconciler::id(), VStatefulSetReconciler::c())
    }

    proof fn safety_guarantee_holds(spec: TempPred<ClusterState>, cluster: Cluster)
    ensures
        spec.entails(Self::c().safety_guarantee),
    {
        assume(false);
    }

    proof fn safety_rely_holds(spec: TempPred<ClusterState>, cluster: Cluster)
    ensures
        forall |i| #[trigger] Self::composed().contains_key(i) ==>
            spec.entails((Self::c().safety_partial_rely)(i))
            && spec.entails((Self::composed()[i].safety_partial_rely)(Self::id()))
    {
        assume(false);
    }
}


}
