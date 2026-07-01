use crate::kubernetes_cluster::spec::cluster::*;
use verus_temporal_logic::defs::*;
use verus_temporal_logic::rules::*;
use crate::kubernetes_cluster::proof::composition::*;
use vstd::prelude::*;

verus! {

pub struct CoreCluster {
    pub cluster: Cluster,
    pub registry: Map<int, ControllerSpec>,
}

pub struct CoreSet {
    pub members: Set<int>,
    pub liveness_dependency: TempPred<ClusterState>,
}

// cluster_model is the paper's M_S: a pure temporal predicate describing
// the cluster's init/next/fairness. Well-formedness of the registry vs.
// the cluster config lives in `well_formed`, not here.
pub open spec fn cluster_model(cluster: CoreCluster) -> TempPred<ClusterState> {
    lift_state(cluster.cluster.init())
    .and(always(lift_action(cluster.cluster.next())))
    .and(tla_forall(|i: int| if cluster.registry.contains_key(i) { (cluster.registry[i].fairness)(cluster.cluster) } else { true_pred() }))
}

// well_formed is a structural constraint on the CoreCluster/CoreSet pair:
// (1) every member of S is in the registry (so registry[i] is meaningful),
// (2) every member's membership predicate holds against cluster.
pub open spec fn well_formed(cluster: CoreCluster, s: CoreSet) -> bool {
    &&& forall |i: int| #[trigger] s.members.contains(i) ==> cluster.registry.contains_key(i)
    &&& forall |i: int| #[trigger] s.members.contains(i) ==> (cluster.registry[i].membership)(cluster.cluster, i)
}

pub open spec fn core(cluster: CoreCluster, s: CoreSet) -> bool {
    let G = tla_forall(|c: int| if s.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred() });
    let R = tla_forall(|pair: (int, int)| if s.members.contains(pair.0) && !s.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred() });
    let environment_rely = tla_forall(| c: int | if s.members.contains(c) { cluster.registry[c].environment_rely } else { true_pred() });
    let ESR = tla_forall(|c: int| if s.members.contains(c) { cluster.registry[c].esr } else { true_pred() });
    cluster_model(cluster).entails(G.and(R.and(s.liveness_dependency).and(environment_rely).implies(ESR)))
}

pub open spec fn union_coreset(s1: CoreSet, s2: CoreSet, liveness_dependency: TempPred<ClusterState>) -> CoreSet {
    CoreSet {
        members: s1.members.union(s2.members),
        liveness_dependency: liveness_dependency
    }
}

pub open spec fn compatible(cluster: CoreCluster, s1: CoreSet, s2: CoreSet) -> bool {
    let g_s1 = tla_forall(|c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred() });
    let g_s2 = tla_forall(|c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred() });
    let r_12 = tla_forall(|pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred() });
    let r_21 = tla_forall(|pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred() });
    cluster_model(cluster).entails(g_s1.implies(r_21).and(g_s2.implies(r_12)))
}

pub proof fn compose(cluster: CoreCluster, s1: CoreSet, s2: CoreSet)
    requires
        well_formed(cluster, s1),
        well_formed(cluster, s2),
        core(cluster, s1),
        core(cluster, s2),
        valid(s1.liveness_dependency),
        valid(s2.liveness_dependency),
        compatible(cluster, s1, s2)
    ensures
        well_formed(cluster, union_coreset(s1, s2, true_pred())),
        core(cluster, union_coreset(s1, s2, true_pred()))
{
    let spec = cluster_model(cluster);
    let esr_s1 = tla_forall(|c: int| if s1.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() });

    // valid(s2.liveness_dependency) means s1's ESR vacuously implies it
    vacuous_implies(spec, esr_s1, s2.liveness_dependency);
    compose_dep(cluster, s1, s2);
}

// s1 satisfies s2's liveness dependency
pub open spec fn satisfies_dependency(cluster: CoreCluster, s1: CoreSet, s2: CoreSet) -> bool {
    let esr_s1 = tla_forall(|c: int| if s1.members.contains(c) { cluster.registry[c].esr } else { true_pred() });
    cluster_model(cluster).entails(esr_s1.implies(s2.liveness_dependency))
}

pub proof fn compose_dep(cluster: CoreCluster, s1: CoreSet, s2: CoreSet)
    requires
        well_formed(cluster, s1),
        well_formed(cluster, s2),
        core(cluster, s1),
        core(cluster, s2),
        compatible(cluster, s1, s2),
        valid(s1.liveness_dependency),
        satisfies_dependency(cluster, s1, s2)
    ensures
        well_formed(cluster, union_coreset(s1, s2, true_pred())),
        core(cluster, union_coreset(s1, s2, true_pred()))
{
    let s = union_coreset(s1, s2, true_pred());
    let spec = cluster_model(cluster);

    assert forall |i: int| #[trigger] s.members.contains(i) implies cluster.registry.contains_key(i) by {
        if s1.members.contains(i) {} else if s2.members.contains(i) {}
    }
    assert forall |i: int| #[trigger] s.members.contains(i) implies (cluster.registry[i].membership)(cluster.cluster, i) by {
        if s1.members.contains(i) {} else if s2.members.contains(i) {}
    }

    let G1_fn = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
    let R1_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
    let ESR1_fn = |c: int| if s1.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
    let environment_rely1 = |c: int| if s1.members.contains(c) { cluster.registry[c].environment_rely } else { true_pred::<ClusterState>() };

    let G2_fn = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
    let R2_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
    let ESR2_fn = |c: int| if s2.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
    let environment_rely2 = |c: int| if s2.members.contains(c) { cluster.registry[c].environment_rely } else { true_pred::<ClusterState>() };

    let Gs_fn = |c: int| if s.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
    let Rs_fn = |pair: (int, int)| if s.members.contains(pair.0) && !s.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
    let ESRs_fn = |c: int| if s.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
    let environment_rely_s = |c: int| if s.members.contains(c) { cluster.registry[c].environment_rely } else { true_pred::<ClusterState>() };

    let R12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
    let R21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };

    let ante1 = tla_forall(R1_fn).and(s1.liveness_dependency).and(tla_forall(environment_rely1));
    let ante2 = tla_forall(R2_fn).and(s2.liveness_dependency).and(tla_forall(environment_rely2));
    let ante = tla_forall(Rs_fn).and(s.liveness_dependency).and(tla_forall(environment_rely_s));

    let goal = tla_forall(Gs_fn).and(ante.implies(tla_forall(ESRs_fn)));
    let f1 = tla_forall(G1_fn).and(ante1.implies(tla_forall(ESR1_fn)));
    let f2 = tla_forall(G2_fn).and(ante2.implies(tla_forall(ESR2_fn)));
    let f3 = tla_forall(G1_fn).implies(tla_forall(R21_fn)).and(tla_forall(G2_fn).implies(tla_forall(R12_fn)));
    let f4 = tla_forall(ESR1_fn).implies(s2.liveness_dependency);

    entails_and(spec, tla_forall(G1_fn), ante1.implies(tla_forall(ESR1_fn)));
    entails_and(spec, tla_forall(G2_fn), ante2.implies(tla_forall(ESR2_fn)));
    entails_and(spec, tla_forall(G1_fn).implies(tla_forall(R21_fn)), tla_forall(G2_fn).implies(tla_forall(R12_fn)));

    // The compatibility implications discharged by the guarantees (modus ponens).
    implies_apply(spec, tla_forall(G1_fn), tla_forall(R21_fn));
    implies_apply(spec, tla_forall(G2_fn), tla_forall(R12_fn));

    // Goal, part 1: spec |= tla_forall(Gs_fn), merging G1 and G2 over the union.
    assert forall |c: int| spec.entails(#[trigger] Gs_fn(c)) by {
        if s1.members.contains(c) {
            tla_forall_apply(G1_fn, c);
            entails_trans(spec, tla_forall(G1_fn), G1_fn(c));
        } else if s2.members.contains(c) {
            tla_forall_apply(G2_fn, c);
            entails_trans(spec, tla_forall(G2_fn), G2_fn(c));
        }
    }
    spec_entails_tla_forall(spec, Gs_fn);

    // Goal, part 2: spec |= ante => tla_forall(ESRs_fn), by the deduction theorem.
    // Reason under spec2 = spec /\ ante and discharge tla_forall(ESRs_fn).
    let spec2 = spec.and(ante);
    entails_and(spec2, spec, ante);
    entails_and(spec2, tla_forall(Rs_fn).and(s.liveness_dependency), tla_forall(environment_rely_s));
    entails_and(spec2, tla_forall(Rs_fn), s.liveness_dependency);

    // Lift the spec-level facts we still need to spec2.
    entails_trans(spec2, spec, tla_forall(R12_fn));
    entails_trans(spec2, spec, tla_forall(R21_fn));
    entails_trans(spec2, spec, ante1.implies(tla_forall(ESR1_fn)));
    entails_trans(spec2, spec, ante2.implies(tla_forall(ESR2_fn)));
    entails_trans(spec2, spec, f4);

    // spec2 |= tla_forall(R1_fn): a partial rely for s1 comes from r_12 (when the
    // other index is in s2) or from the union's rely otherwise.
    assert forall |pair: (int, int)| spec2.entails(#[trigger] R1_fn(pair)) by {
        let (c, c_prime) = pair;
        if s1.members.contains(c) && !s1.members.contains(c_prime) {
            if s2.members.contains(c_prime) {
                tla_forall_apply(R12_fn, pair);
                entails_trans(spec2, tla_forall(R12_fn), R12_fn(pair));
            } else {
                tla_forall_apply(Rs_fn, pair);
                entails_trans(spec2, tla_forall(Rs_fn), Rs_fn(pair));
            }
        }
    }
    spec_entails_tla_forall(spec2, R1_fn);

    // spec2 |= tla_forall(R2_fn): symmetric, using r_21.
    assert forall |pair: (int, int)| spec2.entails(#[trigger] R2_fn(pair)) by {
        let (c, c_prime) = pair;
        if s2.members.contains(c) && !s2.members.contains(c_prime) {
            if s1.members.contains(c_prime) {
                tla_forall_apply(R21_fn, pair);
                entails_trans(spec2, tla_forall(R21_fn), R21_fn(pair));
            } else {
                tla_forall_apply(Rs_fn, pair);
                entails_trans(spec2, tla_forall(Rs_fn), Rs_fn(pair));
            }
        }
    }
    spec_entails_tla_forall(spec2, R2_fn);

    // spec2 |= tla_forall(environment_rely1) and environment_rely2 from environment_rely_s.
    assert forall |c: int| spec2.entails(#[trigger] environment_rely1(c)) by {
        if s1.members.contains(c) {
            tla_forall_apply(environment_rely_s, c);
            entails_trans(spec2, tla_forall(environment_rely_s), environment_rely_s(c));
        }
    }
    spec_entails_tla_forall(spec2, environment_rely1);
    assert forall |c: int| spec2.entails(#[trigger] environment_rely2(c)) by {
        if s2.members.contains(c) {
            tla_forall_apply(environment_rely_s, c);
            entails_trans(spec2, tla_forall(environment_rely_s), environment_rely_s(c));
        }
    }
    spec_entails_tla_forall(spec2, environment_rely2);

    // spec2 |= tla_forall(ESR1_fn): assemble ante1 and discharge f1's implication.
    entails_and(spec2, tla_forall(R1_fn), s1.liveness_dependency);
    entails_and(spec2, tla_forall(R1_fn).and(s1.liveness_dependency), tla_forall(environment_rely1));
    implies_apply(spec2, ante1, tla_forall(ESR1_fn));

    // spec2 |= s2.liveness_dependency via satisfies_dependency (f4), then tla_forall(ESR2_fn).
    implies_apply(spec2, tla_forall(ESR1_fn), s2.liveness_dependency);
    entails_and(spec2, tla_forall(R2_fn), s2.liveness_dependency);
    entails_and(spec2, tla_forall(R2_fn).and(s2.liveness_dependency), tla_forall(environment_rely2));
    implies_apply(spec2, ante2, tla_forall(ESR2_fn));

    // spec2 |= tla_forall(ESRs_fn), merging ESR1 and ESR2 over the union.
    assert forall |c: int| spec2.entails(#[trigger] ESRs_fn(c)) by {
        if s1.members.contains(c) {
            tla_forall_apply(ESR1_fn, c);
            entails_trans(spec2, tla_forall(ESR1_fn), ESR1_fn(c));
        } else if s2.members.contains(c) {
            tla_forall_apply(ESR2_fn, c);
            entails_trans(spec2, tla_forall(ESR2_fn), ESR2_fn(c));
        }
    }
    spec_entails_tla_forall(spec2, ESRs_fn);

    // Discharge the deduction theorem and combine the two goal conjuncts.
    entails_implies(spec, ante, tla_forall(ESRs_fn));
    entails_and(spec, tla_forall(Gs_fn), ante.implies(tla_forall(ESRs_fn)));
}

}
