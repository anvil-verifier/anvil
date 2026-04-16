use crate::composition::vreplicaset_reconciler::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::vd_controller_model, reconciler::*},
    proof::{
        guarantee::*,
        helper_invariants,
        helper_lemmas::*,
        liveness::api_actions::*,
        liveness::{proof as vd_proof, rolling_update::composition::*, spec as vd_spec},
        predicate::*,
    },
    trusted::{liveness_theorem as vd_liveness, rely_guarantee::*, spec_types::*},
};
use crate::vreplicaset_controller::{
    model::{install::vrs_controller_model, reconciler::VReplicaSetReconciler},
    proof::liveness::{proof as vrs_proof, spec as vrs_spec},
    trusted::{liveness_theorem as vrs_liveness, rely_guarantee::*, spec_types::*},
};
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*, string_view::*};
use vstd::{map_lib::*, prelude::*, set_lib::*};

verus! {

impl Composition for VDeploymentReconciler {
    open spec fn c() -> ControllerSpec {
        ControllerSpec{
            esr: vd_liveness::composed_vd_eventually_stable_reconciliation(),
            liveness_dependency: vrs_liveness::vrs_eventually_stable_reconciliation(),
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

    open spec fn id() -> int { 2 }

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
    proof fn esr_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().esr),
    {
        let next_with_wf = always(lift_action(cluster.next())).and(weak_fairness_assumptions(cluster, Self::id()));
        assert(spec.entails(next_with_wf)) by {
            entails_and_temp(spec, always(lift_action(cluster.next())), weak_fairness_assumptions(cluster, Self::id()));
        }
        assert(spec.entails(vd_spec::next_with_wf(cluster, Self::id()))) by {
            entails_trans(spec, next_with_wf, vd_spec::next_with_wf(cluster, Self::id()));
        }
        vd_proof::lemma_vd_composed_eventually_stable_reconciliation(spec, cluster, Self::id());
    }

    proof fn liveness_dependency_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().liveness_dependency),
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
