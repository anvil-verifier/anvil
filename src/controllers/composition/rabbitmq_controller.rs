use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::kubernetes_cluster::spec::message::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::defs::*;
use crate::rabbitmq_controller::trusted::{
    spec_types::*, rely_guarantee::*, liveness_theorem::*, step::*
};
use crate::rabbitmq_controller::model::{
    reconciler::*, install::*, resource::stateful_set::make_stateful_set
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
use crate::temporal_logic::rules::*;

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
            fairness: |cluster: Cluster| next_with_wf(cluster, Self::id()),
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

impl VerticalComposition for RabbitmqReconciler {
    proof fn liveness_guarantee_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().liveness_guarantee),
    {
        assert(spec.entails(vsts_spec::next_with_wf(cluster, Self::id()))) by {
            entails_trans(spec, next_with_wf(cluster, Self::id()), vsts_spec::next_with_wf(cluster, Self::id()));
        }

        assert forall |rmq: RabbitmqClusterView| spec.entails(always(lift_state(#[trigger] Cluster::desired_state_is(rmq))).leads_to(always(lift_state(composed_current_state_matches::<RabbitmqMaker>(rmq))))) by {
            rmq_esr_holds_per_cr(spec, rmq, cluster, Self::id());
            assert(spec.entails(rmq_eventually_stable_reconciliation_per_cr(rmq)));

            let rv = choose |rv: ResourceVersion| rmq_eventually_stable_cm_rv(spec, rmq, rv);
            assert(rmq_eventually_stable_cm_rv(spec, rmq, rv));

            let desired_sts = make_stateful_set(rmq, int_to_string_view(rv));

            leads_to_always_combine(
                spec,
                always(lift_state(Cluster::desired_state_is(rmq))),
                lift_state(current_state_matches::<RabbitmqMaker>(rmq)),
                lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))
            );

            assert(lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))).entails(lift_state(Cluster::desired_state_is(desired_sts)))) by {
                assert forall |ex: Execution<ClusterState>|
                    lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))).satisfied_by(ex)
                    implies #[trigger] lift_state(Cluster::desired_state_is(desired_sts)).satisfied_by(ex) by {
                    let s = ex.head();
                    assert(resource_state_matches::<RabbitmqMaker>(SubResource::StatefulSet, rmq, s));
                    assert(config_map_rv_match::<RabbitmqMaker>(rmq, rv)(s));
                };
            };

            entails_preserved_by_always(
                lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))),
                lift_state(Cluster::desired_state_is(desired_sts))
            );
            entails_implies_leads_to(
                spec,
                always(lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv)))),
                always(lift_state(Cluster::desired_state_is(desired_sts)))
            );
            leads_to_trans(
                spec,
                always(lift_state(Cluster::desired_state_is(rmq))),
                always(lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv)))),
                always(lift_state(Cluster::desired_state_is(desired_sts)))
            );

            let current_state_matches_vsts = |vsts: VStatefulSetView| vsts_liveness_theorem::current_state_matches(vsts);
            assert(spec.entails(Cluster::eventually_stable_reconciliation(current_state_matches_vsts)));
            assert(spec.entails(tla_forall(|vsts: VStatefulSetView| always(lift_state(Cluster::desired_state_is(vsts))).leads_to(always(lift_state(current_state_matches_vsts(vsts)))))));
            use_tla_forall(spec, |vsts: VStatefulSetView| always(lift_state(Cluster::desired_state_is(vsts))).leads_to(always(lift_state(current_state_matches_vsts(vsts)))), desired_sts);

            leads_to_trans(
                spec,
                always(lift_state(Cluster::desired_state_is(rmq))),
                always(lift_state(Cluster::desired_state_is(desired_sts))),
                always(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts)))
            );

            leads_to_always_combine(
                spec,
                always(lift_state(Cluster::desired_state_is(rmq))),
                lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))),
                lift_state(vsts_liveness_theorem::current_state_matches(desired_sts))
            );

            assert(
                lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))).and(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts)))
                .entails(lift_state(composed_current_state_matches::<RabbitmqMaker>(rmq)))
            ) by {
                assert forall |ex: Execution<ClusterState>|
                    lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))).and(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts))).satisfied_by(ex)
                    implies #[trigger] lift_state(composed_current_state_matches::<RabbitmqMaker>(rmq)).satisfied_by(ex) by {
                    let s = ex.head();
                    assert(config_map_rv_match::<RabbitmqMaker>(rmq, rv)(s));
                    assert(composed_vsts_match::<RabbitmqMaker>(rmq)(s));
                };
            };

            entails_preserved_by_always(
                lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))).and(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts))),
                lift_state(composed_current_state_matches::<RabbitmqMaker>(rmq))
            );
            entails_implies_leads_to(
                spec,
                always(lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))).and(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts)))),
                always(lift_state(composed_current_state_matches::<RabbitmqMaker>(rmq)))
            );
            leads_to_trans(
                spec,
                always(lift_state(Cluster::desired_state_is(rmq))),
                always(lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))).and(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts)))),
                always(lift_state(composed_current_state_matches::<RabbitmqMaker>(rmq)))
            );
        }
        let composed_current_state_matches = |rmq: RabbitmqClusterView| composed_current_state_matches::<RabbitmqMaker>(rmq);
        spec_entails_tla_forall(spec, |rmq: RabbitmqClusterView| always(lift_state(Cluster::desired_state_is(rmq))).leads_to(always(lift_state(composed_current_state_matches(rmq)))));
        assert(spec.entails(rmq_composed_eventually_stable_reconciliation()));
    }

    proof fn liveness_rely_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().liveness_rely),
    {
        assert(Self::composed().contains_key(VStatefulSetReconciler::id())); // trigger
    }
}

}
