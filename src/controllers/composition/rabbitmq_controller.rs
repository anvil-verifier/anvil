use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::rabbitmq_controller::trusted::{
    spec_types::*, rely::*, liveness_theorem::*
};
use crate::rabbitmq_controller::model::{
    reconciler::*, install::*
};

use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus !{


// impl Composition for RabbitmqReconciler {
//     open spec fn c() -> ControllerSpec {
//         ControllerSpec{
//             liveness_guarantee: rmq_composed_eventually_stable_reconciliation(),
//             liveness_rely: true_pred(), // VSTS does not require assumptions of other controller's ESR
//             safety_guarantee: always(lift_state(vsts_guarantee(Self::id()))),
//             safety_partial_rely: |other_id: int| always(lift_state(vsts_rely_composition(other_id))),
//             fairness: |cluster: Cluster| next_with_wf(cluster, Self::id()),
//             membership: |cluster: Cluster, id: int| {
//                 &&& cluster.controller_models.contains_pair(id, vsts_controller_model())
//                 &&& cluster.type_is_installed_in_cluster::<VStatefulSetView>()
//             },
//         }
//     }

//     uninterp spec fn id() -> int;

//     open spec fn composed() -> Map<int, ControllerSpec> {
//         Map::empty().insert(Self::id(), Self::c())
//     }

//     proof fn safety_guarantee_holds(spec: TempPred<ClusterState>, cluster: Cluster)
//     ensures
//         spec.entails(Self::c().safety_guarantee),
//     {
//         guarantee_condition_holds(spec, cluster, Self::id());
//     }

//     proof fn safety_rely_holds(spec: TempPred<ClusterState>, cluster: Cluster)
//     ensures
//         forall |i| #[trigger] Self::composed().contains_key(i) ==>
//             spec.entails((Self::c().safety_partial_rely)(i))
//             && spec.entails((Self::composed()[i].safety_partial_rely)(Self::id()))
//     {}
// }


}