use crate::composition::vstatefulset_reconciler::*;
use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::proof::core::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::rabbitmq_controller::model::install::*;
use crate::rabbitmq_controller::proof::{
    composition::composed_rmq_eventually_stable_reconciliation,
    guarantee::guarantee_condition_holds as rmq_guarantee_condition_holds,
    liveness::spec as rmq_spec,
};
use crate::rabbitmq_controller::trusted::{
    liveness_theorem::*, rely_guarantee::*, spec_types::*,
};
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use crate::vstatefulset_controller::trusted::{
    liveness_theorem as vsts_liveness, rely_guarantee::{vsts_guarantee, vsts_rely},
    spec_types::*,
};
use vstd::prelude::*;

verus! {

pub open spec fn rmq_controller_spec(id: int) -> ControllerSpec {
    ControllerSpec {
        esr: rmq_composed_eventually_stable_reconciliation(),
        liveness_dependency: vsts_liveness::vsts_eventually_stable_reconciliation(),
        safety_guarantee: always(lift_state(rmq_guarantee(id))),
        environment_rely: true_pred(),
        safety_partial_rely: |other_id: int| always(lift_state(rmq_rely(other_id))),
        fairness: |cluster: Cluster| rmq_spec::next_with_wf(cluster, id),
        membership: |cluster: Cluster, c_id: int| {
            &&& cluster.controller_models.contains_pair(c_id, rabbitmq_controller_model())
            &&& cluster.type_is_installed_in_cluster::<RabbitmqClusterView>()
            &&& cluster.type_is_installed_in_cluster::<VStatefulSetView>()
        },
    }
}

pub open spec fn rmq_core_set(id: int) -> CoreSet {
    CoreSet {
        members: Set::empty().insert(id),
        liveness_dependency: vsts_liveness::vsts_eventually_stable_reconciliation(),
    }
}

pub proof fn rmq_singleton_core_holds(cluster: CoreCluster, id: int)
    requires
        cluster.registry.contains_pair(id, rmq_controller_spec(id)),
        well_formed(cluster, rmq_core_set(id)),
    ensures
        core(cluster, rmq_core_set(id)),
{
    let s = rmq_core_set(id);
    let spec = cluster_model(cluster);
    let inner = cluster.cluster;

    // Unfold well_formed to get membership facts.
    assert(s.members.contains(id)); // trigger
    assert((cluster.registry[id].membership)(inner, id));

    // Extract spec.entails(next_with_wf(inner, id)) from the fairness tla_forall at i=id.
    let fairness_fn = |i: int| if cluster.registry.contains_key(i) {
        (cluster.registry[i].fairness)(inner)
    } else { true_pred::<ClusterState>() };
    assert(spec.entails(rmq_spec::next_with_wf(inner, id))) by {
        tla_forall_apply(fairness_fn, id);
    }

    // Guarantee
    rmq_guarantee_condition_holds(spec, inner, id);

    let G_fn = |c: int| if s.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
    let R_fn = |pair: (int, int)| if s.members.contains(pair.0) && !s.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
    let ESR_fn = |c: int| if s.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
    let env_fn = |c: int| if s.members.contains(c) { cluster.registry[c].environment_rely } else { true_pred::<ClusterState>() };

    assert forall |c: int| spec.entails(#[trigger] G_fn(c)) by {
        if s.members.contains(c) {
            tla_forall_apply(G_fn, c);
        }
    }
    spec_entails_tla_forall(spec, G_fn);

    // Group R with D (RMQ's liveness depends on VSTS's ESR, so D is non-trivial).
    let assumption_rd = tla_forall(R_fn).and(s.liveness_dependency);
    let spec_rd = spec.and(assumption_rd);

    assert forall |c: int| spec_rd.entails(#[trigger] ESR_fn(c)) by {
        if s.members.contains(c) {
            assert forall |other_id: int| #[trigger] inner.controller_models.remove(id).contains_key(other_id)
                implies spec_rd.entails(always(lift_state(rmq_rely(other_id)))) by {
                tla_forall_apply(R_fn, (id, other_id));
                entails_trans(spec_rd, tla_forall(R_fn), R_fn((id, other_id)));
            }
            entails_trans(spec_rd, spec, lift_state(inner.init()));
            entails_trans(spec_rd, spec, rmq_spec::next_with_wf(inner, id));
            assert(s.liveness_dependency == vsts_liveness::vsts_eventually_stable_reconciliation());
            composed_rmq_eventually_stable_reconciliation(spec_rd, inner, id);
            assert(ESR_fn(c) == rmq_composed_eventually_stable_reconciliation());
        }
    }
    spec_entails_tla_forall(spec_rd, ESR_fn);
    entails_implies(spec, assumption_rd, tla_forall(ESR_fn));

    // Collapse the env factor (trivial for RMQ) so R.and(D).and(env) matches assumption_rd.
    assert(spec.entails(tla_forall(G_fn).and(tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn)).implies(tla_forall(ESR_fn))))) by {
        temp_pred_equality(tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn)), assumption_rd);
        entails_and_temp(spec, tla_forall(G_fn), tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn)).implies(tla_forall(ESR_fn)));
    }
}

pub proof fn vsts_rmq_core_holds(cluster: CoreCluster, vsts_id: int, rmq_id: int)
    requires
        vsts_id != rmq_id,
        cluster.registry.contains_pair(vsts_id, vsts_controller_spec(vsts_id)),
        cluster.registry.contains_pair(rmq_id, rmq_controller_spec(rmq_id)),
        well_formed(cluster, vsts_core_set(vsts_id)),
        well_formed(cluster, rmq_core_set(rmq_id)),
    ensures
        well_formed(cluster, union_coreset(vsts_core_set(vsts_id), rmq_core_set(rmq_id), true_pred())),
        core(cluster, union_coreset(vsts_core_set(vsts_id), rmq_core_set(rmq_id), true_pred())),
{
    let s1 = vsts_core_set(vsts_id);
    let s2 = rmq_core_set(rmq_id);
    let spec = cluster_model(cluster);

    vsts_singleton_core_holds(cluster, vsts_id);
    rmq_singleton_core_holds(cluster, rmq_id);

    // satisfies_dependency(cluster, s1, s2): esr_s1 implies s2.liveness_dependency.
    assert(satisfies_dependency(cluster, s1, s2)) by {
        let esr_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
        let esr_s1 = tla_forall(esr_fn_s1);
        assert(s1.members.contains(vsts_id));
        tla_forall_apply(esr_fn_s1, vsts_id);
        entails_trans(spec.and(esr_s1), esr_s1, s2.liveness_dependency);
        entails_implies(spec, esr_s1, s2.liveness_dependency);
    }

    // compatible(cluster, s1, s2): tla_forall(g_fn_s1) implies tla_forall(r21_fn), tla_forall(g_fn_s2) implies tla_forall(r12_fn).
    assert(compatible(cluster, s1, s2)) by {
        let g_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let g_fn_s2 = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let r12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
        let r21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };

        entails_preserved_by_always(lift_state(vsts_guarantee(vsts_id)), lift_state(rmq_rely(vsts_id)));
        entails_preserved_by_always(lift_state(rmq_guarantee(rmq_id)), lift_state(vsts_rely(rmq_id)));

        // Direction 1: show spec.and(tla_forall(g_fn_s1)).entails(tla_forall(r21_fn)), then entails_implies.
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s1)).entails(#[trigger] r21_fn(pair)) by {
            if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) {
                tla_forall_apply(g_fn_s1, vsts_id);
                entails_trans(spec.and(tla_forall(g_fn_s1)), tla_forall(g_fn_s1), always(lift_state(vsts_guarantee(vsts_id))));
                entails_trans(spec.and(tla_forall(g_fn_s1)), always(lift_state(vsts_guarantee(vsts_id))), always(lift_state(rmq_rely(vsts_id))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s1)), r21_fn);
        entails_implies(spec, tla_forall(g_fn_s1), tla_forall(r21_fn));

        // Direction 2: symmetric.
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
            if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                tla_forall_apply(g_fn_s2, rmq_id);
                entails_trans(spec.and(tla_forall(g_fn_s2)), tla_forall(g_fn_s2), always(lift_state(rmq_guarantee(rmq_id))));
                entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(rmq_guarantee(rmq_id))), always(lift_state(vsts_rely(rmq_id))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s2)), r12_fn);
        entails_implies(spec, tla_forall(g_fn_s2), tla_forall(r12_fn));

        entails_and_temp(spec, tla_forall(g_fn_s1).implies(tla_forall(r21_fn)), tla_forall(g_fn_s2).implies(tla_forall(r12_fn)));
    }

    compose_dep(cluster, s1, s2);
}

}
