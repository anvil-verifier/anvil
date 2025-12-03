use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::{
    cluster::*, message::*
};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::trusted::liveness_theorem as vrs_liveness;
use crate::vdeployment_controller::trusted::liveness_theorem as vd_liveness;
use crate::vreplicaset_controller::trusted::{
    spec_types::*, rely_guarantee::*
};
use crate::vreplicaset_controller::model::reconciler::VReplicaSetReconciler;
use crate::composition::vreplicaset_reconciler::*;
use crate::vdeployment_controller::trusted::{
    spec_types::*, rely_guarantee::*, util::*
};
use crate::vdeployment_controller::model::{
    reconciler::*, install::*
};
use crate::vdeployment_controller::proof::{
    guarantee::*, liveness::{spec::*, proof::*, composition::*}, predicate::*, helper_lemmas::*, helper_invariants, liveness::api_actions::*
};
use crate::vstd_ext::{
    string_view::*, seq_lib::*, set_lib::*, map_lib::*
};
use vstd::{
    prelude::*, set_lib::*, map_lib::*
};

verus !{


impl Composition for VDeploymentReconciler {
    open spec fn c() -> ControllerSpec {
        ControllerSpec{
            liveness_guarantee: composed_vd_eventually_stable_reconciliation(),
            liveness_rely: vrs_liveness::vrs_eventually_stable_reconciliation(),
            safety_guarantee: always(lift_state(vd_guarantee(Self::id()))),
            safety_partial_rely: |other_id: int| always(lift_state(vd_rely(other_id))),
            fairness: |cluster: Cluster| next_with_wf(cluster, Self::id()),
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

    // vrs_guarantee to vd_rely & vrs_rely, trivial
    proof fn safety_rely_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures forall |i| #[trigger] Self::composed().contains_key(i) ==>
            spec.entails((Self::c().safety_partial_rely)(i))
            && spec.entails((Self::composed()[i].safety_partial_rely)(Self::id()))
    {
        let vd_guarantee = vd_guarantee(Self::id());
        let vd_rely = vd_rely(VReplicaSetReconciler::id());
        let vrs_guarantee = vrs_guarantee(VReplicaSetReconciler::id());
        let vrs_rely = vrs_rely(Self::id());
        assert(Self::composed().contains_key(VReplicaSetReconciler::id())); // trigger
        assert(lift_state(vd_guarantee).and(lift_state(vrs_guarantee)).entails(lift_state(vd_rely).and(lift_state(vrs_rely))));
        // spec |= always(p & q)
        entails_and_temp(spec,
            always(lift_state(vd_guarantee)),
            always(lift_state(vrs_guarantee)));
        // always(p) & always(q) == always(p & q)
        always_and_equality(lift_state(vd_guarantee), lift_state(vrs_guarantee));
        // spec |= always(p & q) && p & q |= r & s ==> spec |= always(r & s)
        always_weaken(spec, lift_state(vd_guarantee).and(lift_state(vrs_guarantee)), lift_state(vd_rely).and(lift_state(vrs_rely)));
        // always(r) & always(s) == always(r & s)
        always_and_equality(lift_state(vd_rely), lift_state(vrs_rely));
        entails_trans(spec, // spec |= always(r & s) |= always(r)
            always(lift_state(vd_rely)).and(always(lift_state(vrs_rely))),
            always(lift_state(vd_rely))
        );
        entails_trans(spec, // spec |= always(r & s) |= always(s)
            always(lift_state(vd_rely)).and(always(lift_state(vrs_rely))),
            always(lift_state(vrs_rely))
        );
    }
}

impl VerticalComposition for VDeploymentReconciler {
    proof fn liveness_guarantee_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().liveness_guarantee),
    {
        eventually_stable_reconciliation_holds(spec, cluster, Self::id());
        assume(vrs_liveness::vrs_eventually_stable_reconciliation() ==
            tla_forall(|vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(current_state_matches_vrs()(vrs))))));
        assume(vd_liveness::vd_eventually_stable_reconciliation(Self::id()) ==
            tla_forall(|vd: VDeploymentView| always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(vd_liveness::current_state_matches(vd))))));
        assert forall |vrs| #[trigger] spec.entails(always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(current_state_matches_vrs()(vrs))))) by {
            use_tla_forall(spec, |vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(current_state_matches_vrs()(vrs)))), vrs);
        }
        assert forall |vd: VDeploymentView| #[trigger] spec.entails(always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(vd_liveness::current_state_matches(vd))))) by {
            use_tla_forall(spec, |vd: VDeploymentView| always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(vd_liveness::current_state_matches(vd)))), vd);
        }
        assert forall |vd| #[trigger] spec.entails(always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(composed_current_state_matches(vd))))) by {
            // TODO: import reachability proof of inductive_current_state_matches
            assume(spec.entails(always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(lift_state(vd_liveness::inductive_current_state_matches(vd, Self::id())))));
            assume(spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, Self::id())))));
            assume(spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(Self::id()))));
            vrs_set_matches_vd_stable_state_leads_to_composed_current_state_matches_vd(spec, vd, Self::id(), cluster);
        }
        spec_entails_tla_forall(spec, |vd| always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(composed_current_state_matches(vd)))));
        assume(composed_vd_eventually_stable_reconciliation() ==
            tla_forall(|vd| always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(composed_current_state_matches(vd))))));
    }

    proof fn liveness_rely_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().liveness_rely),
    {
        assert(Self::composed().contains_key(VReplicaSetReconciler::id())); // trigger
    }
}

}