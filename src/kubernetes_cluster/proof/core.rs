use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
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
    let s = union_coreset(s1, s2, true_pred());
    let spec = cluster_model(cluster);

    // well_formed for the union follows from well_formed on each side.
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

    assert(spec.entails(tla_forall(Gs_fn).and(tla_forall(Rs_fn).and(s.liveness_dependency).and(tla_forall(environment_rely_s)).implies(tla_forall(ESRs_fn))))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] spec.satisfied_by(ex) implies
            tla_forall(Gs_fn).and(tla_forall(Rs_fn).and(s.liveness_dependency).and(tla_forall(environment_rely_s)).implies(tla_forall(ESRs_fn))).satisfied_by(ex) by {

            entails_apply(ex, spec, tla_forall(G1_fn).and(tla_forall(R1_fn).and(s1.liveness_dependency).and(tla_forall(environment_rely1)).implies(tla_forall(ESR1_fn))));
            entails_apply(ex, spec, tla_forall(G2_fn).and(tla_forall(R2_fn).and(s2.liveness_dependency).and(tla_forall(environment_rely2)).implies(tla_forall(ESR2_fn))));
            entails_apply(ex, spec, tla_forall(G1_fn).implies(tla_forall(R21_fn)).and(tla_forall(G2_fn).implies(tla_forall(R12_fn))));

            assert(tla_forall(Gs_fn).satisfied_by(ex)) by {
                assert forall |c: int| #[trigger] Gs_fn(c).satisfied_by(ex) by {
                    if s1.members.contains(c) {
                        tla_forall_unfold(ex, G1_fn);
                        assert(G1_fn(c).satisfied_by(ex));
                    } else if s2.members.contains(c) {
                        tla_forall_unfold(ex, G2_fn);
                        assert(G2_fn(c).satisfied_by(ex));
                    }
                }
            }

            if tla_forall(Rs_fn).and(tla_forall(environment_rely_s)).satisfied_by(ex) {
                assert(tla_forall(R1_fn).satisfied_by(ex)) by {
                    assert forall |pair: (int, int)| #[trigger] R1_fn(pair).satisfied_by(ex) by {
                        let (c, c_prime) = pair;
                        if s1.members.contains(c) && !s1.members.contains(c_prime) {
                            if s2.members.contains(c_prime) {
                                tla_forall_unfold(ex, R12_fn); assert(R12_fn((c, c_prime)).satisfied_by(ex));
                            } else {
                                tla_forall_unfold(ex, Rs_fn); assert(Rs_fn((c, c_prime)).satisfied_by(ex));
                            }
                        }
                    }
                }
                assert(tla_forall(R2_fn).satisfied_by(ex)) by {
                    assert forall |pair: (int, int)| #[trigger] R2_fn(pair).satisfied_by(ex) by {
                        let (c, c_prime) = pair;
                        if s2.members.contains(c) && !s2.members.contains(c_prime) {
                            if s1.members.contains(c_prime) {
                                tla_forall_unfold(ex, R21_fn); assert(R21_fn((c, c_prime)).satisfied_by(ex));
                            } else {
                                tla_forall_unfold(ex, Rs_fn); assert(Rs_fn((c, c_prime)).satisfied_by(ex));
                            }
                        }
                    }
                }

                assert(tla_forall(environment_rely1).satisfied_by(ex)) by {
                    assert forall |c: int| #[trigger] environment_rely1(c).satisfied_by(ex) by {
                        if s.members.contains(c) {
                            tla_forall_unfold(ex, environment_rely_s);
                            assert(environment_rely_s(c).satisfied_by(ex));
                        } else {

                        }
                    }
                }

                assert(tla_forall(environment_rely2).satisfied_by(ex)) by {
                    assert forall |c: int| #[trigger] environment_rely2(c).satisfied_by(ex) by {
                        if s.members.contains(c) {
                            tla_forall_unfold(ex, environment_rely_s);
                            assert(environment_rely_s(c).satisfied_by(ex));
                        } else {

                        }
                    }
                }

                assert(tla_forall(ESRs_fn).satisfied_by(ex)) by {
                    assert forall |c: int| #[trigger] ESRs_fn(c).satisfied_by(ex) by {
                        if s1.members.contains(c) {
                            tla_forall_unfold(ex, ESR1_fn);
                            assert(ESR1_fn(c).satisfied_by(ex));
                        } else if s2.members.contains(c) {
                            tla_forall_unfold(ex, ESR2_fn);
                            assert(ESR2_fn(c).satisfied_by(ex));
                        }
                    }
                }
            }
        }
    }
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

    assert(spec.entails(tla_forall(Gs_fn).and(tla_forall(Rs_fn).and(s.liveness_dependency).and(tla_forall(environment_rely_s)).implies(tla_forall(ESRs_fn))))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] spec.satisfied_by(ex) implies
            tla_forall(Gs_fn).and(tla_forall(Rs_fn).and(s.liveness_dependency).and(tla_forall(environment_rely_s)).implies(tla_forall(ESRs_fn))).satisfied_by(ex) by {

            entails_apply(ex, spec, tla_forall(G1_fn).and(tla_forall(R1_fn).and(s1.liveness_dependency).and(tla_forall(environment_rely1)).implies(tla_forall(ESR1_fn))));
            entails_apply(ex, spec, tla_forall(G2_fn).and(tla_forall(R2_fn).and(s2.liveness_dependency).and(tla_forall(environment_rely2)).implies(tla_forall(ESR2_fn))));
            entails_apply(ex, spec, tla_forall(G1_fn).implies(tla_forall(R21_fn)).and(tla_forall(G2_fn).implies(tla_forall(R12_fn))));
            entails_apply(ex, spec, tla_forall(ESR1_fn).implies(s2.liveness_dependency));

            assert(tla_forall(Gs_fn).satisfied_by(ex)) by {
                assert forall |c: int| #[trigger] Gs_fn(c).satisfied_by(ex) by {
                    if s1.members.contains(c) {
                        tla_forall_unfold(ex, G1_fn);
                        assert(G1_fn(c).satisfied_by(ex));
                    } else if s2.members.contains(c) {
                        tla_forall_unfold(ex, G2_fn);
                        assert(G2_fn(c).satisfied_by(ex));
                    }
                }
            }

            if tla_forall(Rs_fn).and(tla_forall(environment_rely_s)).satisfied_by(ex) {
                assert(tla_forall(R1_fn).satisfied_by(ex)) by {
                    assert forall |pair: (int, int)| #[trigger] R1_fn(pair).satisfied_by(ex) by {
                        let (c, c_prime) = pair;
                        if s1.members.contains(c) && !s1.members.contains(c_prime) {
                            if s2.members.contains(c_prime) {
                                tla_forall_unfold(ex, R12_fn); assert(R12_fn((c, c_prime)).satisfied_by(ex));
                            } else {
                                tla_forall_unfold(ex, Rs_fn); assert(Rs_fn((c, c_prime)).satisfied_by(ex));
                            }
                        }
                    }
                }
                assert(tla_forall(R2_fn).satisfied_by(ex)) by {
                    assert forall |pair: (int, int)| #[trigger] R2_fn(pair).satisfied_by(ex) by {
                        let (c, c_prime) = pair;
                        if s2.members.contains(c) && !s2.members.contains(c_prime) {
                            if s1.members.contains(c_prime) {
                                tla_forall_unfold(ex, R21_fn); assert(R21_fn((c, c_prime)).satisfied_by(ex));
                            } else {
                                tla_forall_unfold(ex, Rs_fn); assert(Rs_fn((c, c_prime)).satisfied_by(ex));
                            }
                        }
                    }
                }

                assert(tla_forall(environment_rely1).satisfied_by(ex)) by {
                    assert forall |c: int| #[trigger] environment_rely1(c).satisfied_by(ex) by {
                        if s.members.contains(c) {
                            tla_forall_unfold(ex, environment_rely_s);
                            assert(environment_rely_s(c).satisfied_by(ex));
                        }
                    }
                }

                assert(tla_forall(environment_rely2).satisfied_by(ex)) by {
                    assert forall |c: int| #[trigger] environment_rely2(c).satisfied_by(ex) by {
                        if s.members.contains(c) {
                            tla_forall_unfold(ex, environment_rely_s);
                            assert(environment_rely_s(c).satisfied_by(ex));
                        }
                    }
                }

                assert(tla_forall(ESRs_fn).satisfied_by(ex)) by {
                    assert forall |c: int| #[trigger] ESRs_fn(c).satisfied_by(ex) by {
                        if s1.members.contains(c) {
                            tla_forall_unfold(ex, ESR1_fn);
                            assert(ESR1_fn(c).satisfied_by(ex));
                        } else if s2.members.contains(c) {
                            tla_forall_unfold(ex, ESR2_fn);
                            assert(ESR2_fn(c).satisfied_by(ex));
                        }
                    }
                }
            }
        }
    }
}

}
