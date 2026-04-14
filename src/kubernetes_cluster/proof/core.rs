use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

// A controller's compositional spec includes
// (1) guarantee conditions (e.g., ESR),
// (2) rely conditions (e.g., non-interference by other controllers),
// (3) fairness conditions (e.g., weak fairness),
// (4) membership conditions (e.g., the CR is installed).
pub struct ControllerSpec {
    pub liveness_guarantee: TempPred<ClusterState>,
    pub liveness_rely: TempPred<ClusterState>,
    pub safety_guarantee: TempPred<ClusterState>,
    // safety_partial_rely takes a controller id (int) and returns a (safety) condition
    // stating that the input controller never interferes with our controller.
    // The safety-rely condition is formalized as a conjunction of safety_partial_rely
    // on all other controller ids in the environment.
    pub safety_partial_rely: spec_fn(int) -> TempPred<ClusterState>,
    pub fairness: spec_fn(Cluster) -> TempPred<ClusterState>,
    pub membership: spec_fn(Cluster, int) -> bool,
}

pub struct CoreSet {
    pub controllers: Set<int>,
    pub dependence: TempPred<ClusterState>,
}

pub open spec fn core_model(spec: TempPred<ClusterState>, cluster: Cluster, specs: Map<int, ControllerSpec>, S: CoreSet) -> bool {
    // the paper formalizes this in terms of S' disjoint from S
    // we just say for all controller IDs not in S
    let R_S = forall |c: int, c_prime: int| (#[trigger] S.controllers.contains(c) &&  ! #[trigger] S.controllers.contains(c_prime)) ==> spec.entails((specs[c].safety_partial_rely)(c_prime));
    let ESR_S = forall |c: int| (#[trigger] S.controllers.contains(c)) ==> spec.entails(specs[c].liveness_guarantee);
    let G_S = forall |c: int| (#[trigger] S.controllers.contains(c)) ==> spec.entails(specs[c].safety_guarantee);
    let D_S= spec.entails(S.dependence);
    G_S && ((R_S && D_S) ==> ESR_S)
}

pub open spec fn cluster_model(model: TempPred<ClusterState>, cluster: Cluster, specs: Map<int, ControllerSpec>) -> bool {
    &&& model.entails(lift_state(cluster.init()))
    &&& model.entails(always(lift_action(cluster.next())))
    &&& forall |i: int| #[trigger] cluster.controller_models.contains_key(i) ==> model.entails((specs[i].fairness)(cluster))
}

pub open spec fn core(cluster: Cluster, specs: Map<int, ControllerSpec>, S: CoreSet) -> bool {
    forall |model: TempPred<ClusterState>| #[trigger] cluster_model(model, cluster, specs) ==> core_model(model, cluster, specs, S)
}

pub open spec fn core_star(cluster: Cluster, specs: Map<int, ControllerSpec>, S: CoreSet) -> bool {
    &&& core(cluster, specs, S)
    &&& valid(S.dependence)
}

pub open spec fn cluster_contains_coreset(cluster: Cluster, specs: Map<int, ControllerSpec>, S: CoreSet) -> bool {
    forall |c: int| #[trigger] S.controllers.contains(c) ==> (specs[c].membership)(cluster, c)
}

pub open spec fn core_star_model(spec: TempPred<ClusterState>, cluster: Cluster, specs: Map<int, ControllerSpec>, S: CoreSet) -> bool {
    &&& core_model(spec, cluster, specs, S)
    &&& valid(S.dependence)
}

// this will discard any liveness dependencies
pub open spec fn union(S1: CoreSet, S2: CoreSet) -> CoreSet {
    CoreSet {
        controllers: S1.controllers.union(S2.controllers),
        dependence: true_pred()
    }
}

pub open spec fn compatible_model(spec: TempPred<ClusterState>, cluster: Cluster, specs: Map<int, ControllerSpec>, S1: CoreSet, S2: CoreSet) -> bool {
    let G_S1 = forall |c: int| (#[trigger] S1.controllers.contains(c)) ==> spec.entails(specs[c].safety_guarantee);
    let G_S2 = forall |c: int| (#[trigger] S2.controllers.contains(c)) ==> spec.entails(specs[c].safety_guarantee);

    let R_12 = forall |c1: int, c2: int| (#[trigger] S1.controllers.contains(c1) && ! #[trigger] S1.controllers.contains(c2) && S2.controllers.contains(c2)) ==> spec.entails((specs[c1].safety_partial_rely)(c2));
    let R_21 = forall |c1: int, c2: int| (#[trigger] S2.controllers.contains(c1) && ! #[trigger] S2.controllers.contains(c2) && S1.controllers.contains(c2)) ==> spec.entails((specs[c1].safety_partial_rely)(c2));

    (G_S1 ==> R_21) && (G_S2 ==> R_12)
}

pub open spec fn compatible(cluster: Cluster, specs: Map<int, ControllerSpec>, S1: CoreSet, S2: CoreSet) -> bool {
    forall |model: TempPred<ClusterState>| #[trigger] cluster_model(model, cluster, specs) ==> compatible_model(model, cluster, specs, S1, S2)
}

// S1 satisfies S2's liveness dependency
pub open spec fn satisfies_dependency_model(spec: TempPred<ClusterState>, cluster: Cluster, specs: Map<int, ControllerSpec>, S1: CoreSet, S2: CoreSet) -> bool {
    let ESR_S1 = forall |c: int| (#[trigger] S1.controllers.contains(c)) ==> spec.entails(specs[c].liveness_guarantee);
    let D_S2 = spec.entails(S2.dependence);
    ESR_S1 ==> D_S2
}

pub proof fn compose_model(spec: TempPred<ClusterState>, cluster: Cluster, specs: Map<int, ControllerSpec>, S1: CoreSet, S2: CoreSet)
    requires
        core_star_model(spec, cluster, specs, S1),
        core_star_model(spec, cluster, specs, S2),
        compatible_model(spec, cluster, specs, S1, S2)
    ensures
        core_star_model(spec, cluster, specs, union(S1, S2))
{
    let s = union(S1, S2);

    assert(valid(s.dependence));

    assert(forall |c: int| #[trigger] s.controllers.contains(c)
        ==> spec.entails(specs[c].safety_guarantee)) by {
        assert forall |c: int| #[trigger] s.controllers.contains(c)
        implies spec.entails(specs[c].safety_guarantee) by {
            if S1.controllers.contains(c) {

            } else {
                assert(S2.controllers.contains(c));
            }
        }
    }

    let r_s = forall |c: int, c_prime: int|
        (#[trigger] s.controllers.contains(c) && !#[trigger] s.controllers.contains(c_prime))
        ==> spec.entails((specs[c].safety_partial_rely)(c_prime));

    if r_s {
        assert(spec.entails(S1.dependence));
        assert(spec.entails(S2.dependence));

        assert(forall |c: int, c_prime: int|
            (#[trigger] S1.controllers.contains(c) && !#[trigger] S1.controllers.contains(c_prime))
            ==> spec.entails((specs[c].safety_partial_rely)(c_prime))) by {
            assert forall |c: int, c_prime: int|
                (#[trigger] S1.controllers.contains(c) && !#[trigger] S1.controllers.contains(c_prime))
            implies spec.entails((specs[c].safety_partial_rely)(c_prime)) by {
                if S2.controllers.contains(c_prime) {

                } else {
                    assert(s.controllers.contains(c));
                    assert(!s.controllers.contains(c_prime));
                }
            }
        }

        assert(forall |c: int| #[trigger] S1.controllers.contains(c)
            ==> spec.entails(specs[c].liveness_guarantee));

        assert(forall |c: int, c_prime: int|
            (#[trigger] S2.controllers.contains(c) && !#[trigger] S2.controllers.contains(c_prime))
            ==> spec.entails((specs[c].safety_partial_rely)(c_prime))) by {
            assert forall |c: int, c_prime: int|
                (#[trigger] S2.controllers.contains(c) && !#[trigger] S2.controllers.contains(c_prime))
            implies spec.entails((specs[c].safety_partial_rely)(c_prime)) by {
                if S1.controllers.contains(c_prime) {

                } else {
                    assert(s.controllers.contains(c));
                    assert(!s.controllers.contains(c_prime));
                }
            }
        }

        assert(forall |c: int| #[trigger] S2.controllers.contains(c)
            ==> spec.entails(specs[c].liveness_guarantee));

        assert(forall |c: int| #[trigger] s.controllers.contains(c)
            ==> spec.entails(specs[c].liveness_guarantee)) by {
            assert forall |c: int| #[trigger] s.controllers.contains(c)
            implies spec.entails(specs[c].liveness_guarantee) by {
                if S1.controllers.contains(c) {
                } else {
                    assert(S2.controllers.contains(c));
                }
            }
        }
    }
}

pub proof fn compose(specs: Map<int, ControllerSpec>, S1: CoreSet, S2: CoreSet)
    requires
        forall |cluster: Cluster| #[trigger] cluster_contains_coreset(cluster, specs, S1) ==> core_star(cluster, specs, S1),
        forall |cluster: Cluster| #[trigger] cluster_contains_coreset(cluster, specs, S2) ==> core_star(cluster, specs, S2),
        forall |cluster: Cluster| #[trigger] cluster_contains_coreset(cluster, specs, union(S1, S2)) ==> compatible(cluster, specs, S1, S2),
    ensures
        forall |cluster: Cluster| #[trigger] cluster_contains_coreset(cluster, specs, union(S1, S2)) ==> core_star(cluster, specs, union(S1, S2)),
{
    let s = union(S1, S2);

    assert forall |cluster: Cluster| #[trigger] cluster_contains_coreset(cluster, specs, s)
    implies core_star(cluster, specs, s) by {
        assert(cluster_contains_coreset(cluster, specs, S1)) by {
            assert forall |c: int| #[trigger] S1.controllers.contains(c)
            implies (specs[c].membership)(cluster, c) by {
                assert(s.controllers.contains(c));
            }
        }

        assert(cluster_contains_coreset(cluster, specs, S2)) by {
            assert forall |c: int| #[trigger] S2.controllers.contains(c)
            implies (specs[c].membership)(cluster, c) by {
                assert(s.controllers.contains(c));
            }
        }

        assert(valid(s.dependence));

        assert(core(cluster, specs, s)) by {
            assert forall |model: TempPred<ClusterState>| #[trigger] cluster_model(model, cluster, specs)
            implies core_model(model, cluster, specs, s) by {
                assert(core_star_model(model, cluster, specs, S1));
                assert(core_star_model(model, cluster, specs, S2));
                assert(compatible_model(model, cluster, specs, S1, S2));
                compose_model(model, cluster, specs, S1, S2);
            }
        }
    }
}

pub proof fn compose_dep_model(spec: TempPred<ClusterState>, cluster: Cluster, specs: Map<int, ControllerSpec>, S1: CoreSet, S2: CoreSet)
    requires
        core_star_model(spec, cluster, specs, S1),
        core_model(spec, cluster, specs, S2),
        compatible_model(spec, cluster, specs, S1, S2),
        satisfies_dependency_model(spec, cluster, specs, S1, S2)
    ensures
        core_star_model(spec, cluster, specs, union(S1, S2))
{
    let s = union(S1, S2);

    assert(valid(s.dependence));

    assert(forall |c: int| #[trigger] s.controllers.contains(c)
        ==> spec.entails(specs[c].safety_guarantee)) by {
        assert forall |c: int| #[trigger] s.controllers.contains(c)
        implies spec.entails(specs[c].safety_guarantee) by {
            if S1.controllers.contains(c) {
            } else {
                assert(S2.controllers.contains(c));
            }
        }
    }

    let r_s = forall |c: int, c_prime: int|
        (#[trigger] s.controllers.contains(c) && !#[trigger] s.controllers.contains(c_prime))
        ==> spec.entails((specs[c].safety_partial_rely)(c_prime));

    if r_s {
        assert(spec.entails(S1.dependence));

        assert(forall |c: int, c_prime: int|
            (#[trigger] S1.controllers.contains(c) && !#[trigger] S1.controllers.contains(c_prime))
            ==> spec.entails((specs[c].safety_partial_rely)(c_prime))) by {
            assert forall |c: int, c_prime: int|
                (#[trigger] S1.controllers.contains(c) && !#[trigger] S1.controllers.contains(c_prime))
            implies spec.entails((specs[c].safety_partial_rely)(c_prime)) by {
                if S2.controllers.contains(c_prime) {
                    // compatible: G_S1 ==> R_12
                } else {
                    assert(s.controllers.contains(c));
                    assert(!s.controllers.contains(c_prime));
                }
            }
        }

        assert(forall |c: int| #[trigger] S1.controllers.contains(c)
            ==> spec.entails(specs[c].liveness_guarantee));

        assert(spec.entails(S2.dependence));

        assert(forall |c: int, c_prime: int|
            (#[trigger] S2.controllers.contains(c) && !#[trigger] S2.controllers.contains(c_prime))
            ==> spec.entails((specs[c].safety_partial_rely)(c_prime))) by {
            assert forall |c: int, c_prime: int|
                (#[trigger] S2.controllers.contains(c) && !#[trigger] S2.controllers.contains(c_prime))
            implies spec.entails((specs[c].safety_partial_rely)(c_prime)) by {
                if S1.controllers.contains(c_prime) {

                } else {
                    assert(s.controllers.contains(c));
                    assert(!s.controllers.contains(c_prime));
                }
            }
        }

        assert(forall |c: int| #[trigger] S2.controllers.contains(c)
            ==> spec.entails(specs[c].liveness_guarantee));

        assert(forall |c: int| #[trigger] s.controllers.contains(c)
            ==> spec.entails(specs[c].liveness_guarantee)) by {
            assert forall |c: int| #[trigger] s.controllers.contains(c)
            implies spec.entails(specs[c].liveness_guarantee) by {
                if S1.controllers.contains(c) {
                } else {
                    assert(S2.controllers.contains(c));
                }
            }
        }
    }
}

}
