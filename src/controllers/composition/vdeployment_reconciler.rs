use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::{
    cluster::*, message::*
};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    trusted::{spec_types::*, rely_guarantee::*, liveness_theorem as vrs_liveness},
    proof::liveness::{proof as vrs_proof, spec as vrs_spec},
    model::{reconciler::VReplicaSetReconciler, install::vrs_controller_model}
};
use crate::composition::vreplicaset_reconciler::*;
use crate::vdeployment_controller::{
    trusted::{spec_types::*, rely_guarantee::*, util::*, liveness_theorem as vd_liveness},
    model::{reconciler::*, install::vd_controller_model},
    proof::{guarantee::*, liveness::{spec as vd_spec, proof as vd_proof, composition::*}, predicate::*, helper_lemmas::*, helper_invariants, liveness::api_actions::*}
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
            liveness_guarantee: vd_liveness::composed_vd_eventually_stable_reconciliation(),
            liveness_rely: vrs_liveness::vrs_eventually_stable_reconciliation(),
            safety_guarantee: always(lift_state(vd_guarantee(Self::id()))),
            safety_partial_rely: |other_id: int| always(lift_state(vd_rely(other_id))),
            fairness: |cluster: Cluster| weak_fairness_assumptions(cluster, Self::id()),
            membership: |cluster: Cluster, id: int| { // id is not used
                &&& cluster.controller_models.contains_pair(VReplicaSetReconciler::id(), vrs_controller_model())
                &&& cluster.controller_models.contains_pair(Self::id(), vd_controller_model())
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
        let next_with_wf = always(lift_action(cluster.next())).and(weak_fairness_assumptions(cluster, Self::id()));
        assert(spec.entails(next_with_wf)) by {
            entails_and_temp(spec, always(lift_action(cluster.next())), weak_fairness_assumptions(cluster, Self::id()));
        }
        assert(spec.entails(vd_spec::next_with_wf(cluster, Self::id()))) by {
            entails_trans(spec, next_with_wf, vd_spec::next_with_wf(cluster, Self::id()));
        }
        let current_state_matches_vrs = |vrs: VReplicaSetView| vrs_liveness::current_state_matches(vrs);
        assert(spec.entails(Cluster::eventually_stable_reconciliation(current_state_matches_vrs)));
        assert(spec.entails(tla_forall(|vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(current_state_matches_vrs(vrs)))))));
        assert forall |vrs| #[trigger] spec.entails(always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs))))) by {
            use_tla_forall(spec, |vrs| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(current_state_matches_vrs(vrs)))), vrs);
        }
        assert forall |vd: VDeploymentView| #[trigger] spec.entails(always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(vd_liveness::inductive_current_state_matches(vd, Self::id()))))) by {
            vd_proof::eventually_stable_reconciliation_holds_per_cr(spec, vd, cluster, Self::id());
        }
        spec_entails_tla_forall(spec, |vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))));
        assert(spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(Self::id())))) by {
            assert forall |vd| #[trigger] spec.entails(always(lift_state(helper_invariants::vd_reconcile_request_only_interferes_with_itself(Self::id(), vd)))) by {
                helper_invariants::lemma_always_vd_reconcile_request_only_interferes_with_itself(spec, cluster, Self::id(), vd);
            }
            spec_entails_tla_forall(spec, |vd| always(lift_state(helper_invariants::vd_reconcile_request_only_interferes_with_itself(Self::id(), vd))));
            spec_entails_always_tla_forall_equality(spec, |vd| lift_state(helper_invariants::vd_reconcile_request_only_interferes_with_itself(Self::id(), vd)));
            only_interferes_with_itself_equivalent_to_lifted_only_interferes_with_itself_action(spec, cluster, Self::id());
        }
        assert forall |vd| #[trigger] spec.entails(always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(vd_liveness::composed_current_state_matches(vd))))) by {
            vd_spec::spec_entails_always_cluster_invariants_since_reconciliation_holds_pre_cr(spec, vd, Self::id(), cluster);
            vrs_set_matches_vd_stable_state_leads_to_composed_current_state_matches_vd(spec, vd, Self::id(), cluster);
        }
        spec_entails_tla_forall(spec, |vd| always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(vd_liveness::composed_current_state_matches(vd)))));
    }

    proof fn liveness_rely_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().liveness_rely),
    {
        assert(Self::composed().contains_key(VReplicaSetReconciler::id())); // trigger
    }
}

pub open spec fn weak_fairness_assumptions(cluster: Cluster, vd_controller_id: int) -> TempPred<ClusterState> {
    tla_forall(|input| cluster.api_server_next().weak_fairness(input))
    .and(tla_forall(|input| cluster.builtin_controllers_next().weak_fairness(input)))
    .and(tla_forall(|input: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((vd_controller_id, input.0, input.1))))
    .and(tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness((vd_controller_id, input))))
    .and(tla_forall(|input| cluster.external_next().weak_fairness((vd_controller_id, input))))
    .and(cluster.disable_crash().weak_fairness(vd_controller_id))
    .and(cluster.disable_req_drop().weak_fairness(()))
    .and(cluster.disable_pod_monkey().weak_fairness(()))
}

}