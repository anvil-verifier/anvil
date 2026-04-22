use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::proof::core::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use crate::vreplicaset_controller::model::{install::*, reconciler::*};
use crate::vreplicaset_controller::proof::{
    guarantee::*,
    liveness::{proof::eventually_stable_reconciliation_holds, spec::*},
};
use crate::vreplicaset_controller::trusted::{
    liveness_theorem::*, rely_guarantee::*, spec_types::*,
};
use vstd::prelude::*;

verus! {

pub open spec fn vrs_controller_spec(id: int) -> ControllerSpec {
    ControllerSpec {
        esr: vrs_eventually_stable_reconciliation(),
        liveness_dependency: true_pred(),
        safety_guarantee: always(lift_state(vrs_guarantee(id))),
        environment_rely: true_pred(),
        safety_partial_rely: |other_id: int| always(lift_state(vrs_rely(other_id))),
        fairness: |cluster: Cluster| next_with_wf(cluster, id),
        membership: |cluster: Cluster, c_id: int| {
            &&& cluster.controller_models.contains_pair(c_id, vrs_controller_model())
            &&& cluster.type_is_installed_in_cluster::<VReplicaSetView>()
        },
    }
}

pub open spec fn vrs_core_set(id: int) -> CoreSet {
    CoreSet {
        members: Set::empty().insert(id),
        liveness_dependency: true_pred(),
    }
}

pub proof fn vrs_singleton_core_holds(cluster: CoreCluster, id: int)
    requires
        cluster.registry.contains_key(id),
        cluster.registry[id] == vrs_controller_spec(id),
        well_formed(cluster, vrs_core_set(id)),
    ensures
        core(cluster, vrs_core_set(id)),
{
    let s = vrs_core_set(id);
    let spec = cluster_model(cluster);
    let inner = cluster.cluster;

    // Unfold well_formed to get membership facts.
    assert(s.members.contains(id));
    assert((cluster.registry[id].membership)(inner, id));
    assert(inner.controller_models.contains_pair(id, vrs_controller_model()));
    assert(inner.type_is_installed_in_cluster::<VReplicaSetView>());

    // Extract spec.entails(init): spec is init ∧ always(next) ∧ fairness_forall.
    assert(spec.entails(lift_state(inner.init()))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] spec.satisfied_by(ex)
            implies lift_state(inner.init()).satisfied_by(ex) by {}
    }

    // Extract spec.entails(always(next)).
    assert(spec.entails(always(lift_action(inner.next())))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] spec.satisfied_by(ex)
            implies always(lift_action(inner.next())).satisfied_by(ex) by {}
    }

    // Extract spec.entails(next_with_wf(inner, id)) from the fairness tla_forall at i=id.
    let fairness_fn = |i: int| if cluster.registry.contains_key(i) {
        (cluster.registry[i].fairness)(inner)
    } else { true_pred::<ClusterState>() };
    assert(spec.entails(next_with_wf(inner, id))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] spec.satisfied_by(ex)
            implies next_with_wf(inner, id).satisfied_by(ex) by {
            assert(tla_forall(fairness_fn).satisfied_by(ex));
            tla_forall_unfold(ex, fairness_fn);
            assert(fairness_fn(id).satisfied_by(ex));
            assert(fairness_fn(id) == (cluster.registry[id].fairness)(inner));
            assert((cluster.registry[id].fairness)(inner) == next_with_wf(inner, id));
        }
    }

    // G side: spec entails always(vrs_guarantee(id)).
    guarantee_condition_holds(spec, inner, id);

    let G_fn = |c: int| if s.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
    let R_fn = |pair: (int, int)| if s.members.contains(pair.0) && !s.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
    let ESR_fn = |c: int| if s.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
    let env_fn = |c: int| if s.members.contains(c) { cluster.registry[c].environment_rely } else { true_pred::<ClusterState>() };

    // ESR side: build spec_r = spec ∧ R, then use eventually_stable_reconciliation_holds.
    let spec_r = spec.and(tla_forall(R_fn));

    // spec_r inherits spec's basic entailments.
    assert(spec_r.entails(lift_state(inner.init()))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] spec_r.satisfied_by(ex)
            implies lift_state(inner.init()).satisfied_by(ex) by {
            entails_apply(ex, spec, lift_state(inner.init()));
        }
    }
    assert(spec_r.entails(next_with_wf(inner, id))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] spec_r.satisfied_by(ex)
            implies next_with_wf(inner, id).satisfied_by(ex) by {
            entails_apply(ex, spec, next_with_wf(inner, id));
        }
    }

    // Rely hypothesis on spec_r: for each other_id in controller_models.remove(id),
    // spec_r entails always(vrs_rely(other_id)).
    assert forall |other_id: int| #[trigger] inner.controller_models.remove(id).contains_key(other_id)
        implies spec_r.entails(always(lift_state(vrs_rely(other_id)))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] spec_r.satisfied_by(ex)
            implies always(lift_state(vrs_rely(other_id))).satisfied_by(ex) by {
            assert(tla_forall(R_fn).satisfied_by(ex));
            tla_forall_unfold(ex, R_fn);
            assert(other_id != id);
            assert(!s.members.contains(other_id));
            assert(R_fn((id, other_id)).satisfied_by(ex));
        }
    }

    eventually_stable_reconciliation_holds(spec_r, inner, id);
    // spec_r.entails(vrs_eventually_stable_reconciliation())

    // Now assemble the core formula.
    let G = tla_forall(G_fn);
    let R = tla_forall(R_fn);
    let env_rely = tla_forall(env_fn);
    let ESR = tla_forall(ESR_fn);

    assert(spec.entails(G.and(R.and(s.liveness_dependency).and(env_rely).implies(ESR)))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] spec.satisfied_by(ex)
            implies G.and(R.and(s.liveness_dependency).and(env_rely).implies(ESR)).satisfied_by(ex) by {

            // G: safety guarantee for every c in s.members.
            entails_apply(ex, spec, always(lift_state(vrs_guarantee(id))));
            assert(G.satisfied_by(ex)) by {
                assert forall |c: int| #[trigger] G_fn(c).satisfied_by(ex) by {
                    if s.members.contains(c) {
                        assert(c == id);
                        assert(cluster.registry[c] == vrs_controller_spec(id));
                        assert(G_fn(c) == always(lift_state(vrs_guarantee(id))));
                    }
                }
            }

            // Implication: assume R ∧ D ∧ Env, conclude ESR.
            if R.and(s.liveness_dependency).and(env_rely).satisfied_by(ex) {
                assert(spec_r.satisfied_by(ex));
                entails_apply(ex, spec_r, vrs_eventually_stable_reconciliation());
                assert(ESR.satisfied_by(ex)) by {
                    assert forall |c: int| #[trigger] ESR_fn(c).satisfied_by(ex) by {
                        if s.members.contains(c) {
                            assert(c == id);
                            assert(cluster.registry[c] == vrs_controller_spec(id));
                            assert(ESR_fn(c) == vrs_eventually_stable_reconciliation());
                        }
                    }
                }
            }
        }
    }
}

}
