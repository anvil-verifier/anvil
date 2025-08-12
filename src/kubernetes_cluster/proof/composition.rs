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
    pub fairness: spec_fn(int) -> TempPred<ClusterState>,
    pub membership: spec_fn(Cluster, int) -> bool,
}

// composable says that when the controllers run together (with other controllers)
// (1) all controllers' safety_guarantee hold, and
// (2) all controllers' liveness_guarantee hold assuming fairness and that other controllers don't interfere with them.
pub open spec fn composable(spec: TempPred<ClusterState>, cluster: Cluster, composition: Map<int, ControllerSpec>) -> bool {
    &&& (forall |i| #[trigger] composition.contains_key(i)
        ==> (composition[i].membership)(cluster, i))
        && spec.entails(lift_state(cluster.init()))
        && spec.entails(always(lift_action(cluster.next())))
        ==> (forall |i| #[trigger] composition.contains_key(i)
            ==> spec.entails(composition[i].safety_guarantee))
    &&& (forall |i| #[trigger] composition.contains_key(i)
        ==> (composition[i].membership)(cluster, i))
        && spec.entails(lift_state(cluster.init()))
        && spec.entails(always(lift_action(cluster.next())))
        && (forall |i| #[trigger] composition.contains_key(i) ==> spec.entails((composition[i].fairness)(i)))
        && (forall |i| #[trigger] composition.contains_key(i)
            ==> forall |j| #[trigger] cluster.controller_models.remove_keys(composition.dom()).contains_key(j)
                ==> spec.entails((composition[i].safety_partial_rely)(j)))
        ==> (forall |i| #[trigger] composition.contains_key(i) ==> spec.entails(composition[i].liveness_guarantee))
}

pub trait Composition: Sized {
    // The spec of the controller we want to compose
    spec fn c() -> ControllerSpec;

    // safety_guarantee of the new controller holds
    proof fn safety_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster, id: int)
        requires
            (Self::c().membership)(cluster, id),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
        ensures
            spec.entails(Self::c().safety_guarantee),
        ;

    // The new controller doesn't interfere with composed controllers, or
    // they satisfy each other's safety_partial_rely
    proof fn no_internal_interference(spec: TempPred<ClusterState>, cluster: Cluster, id: int, composed: Map<int, ControllerSpec>)
        requires
            (Self::c().membership)(cluster, id),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            spec.entails(Self::c().safety_guarantee),
            !composed.contains_key(id),
            forall |i| #[trigger] composed.contains_key(i) ==> (composed[i].membership)(cluster, i),
            forall |i| #[trigger] composed.contains_key(i) ==> spec.entails(composed[i].safety_guarantee),
        ensures
            forall |i| #[trigger] composed.contains_key(i) ==>
                spec.entails((Self::c().safety_partial_rely)(i))
                && spec.entails((composed[i].safety_partial_rely)(id))
        ;
}

pub trait HorizontalComposition: Sized + Composition {
    // For HorizontalComposition, the new controller's liveness doesn't depend on
    // other controllers' liveness
    proof fn liveness_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster, id: int)
        requires
            (Self::c().membership)(cluster, id),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            spec.entails((Self::c().fairness)(id)),
            forall |other_id| #[trigger] cluster.controller_models.remove(id).contains_key(other_id)
                ==> spec.entails((Self::c().safety_partial_rely)(other_id)),
        ensures
            spec.entails(Self::c().liveness_guarantee),
        ;
}

pub trait VerticalComposition: Sized + Composition {
    // For VerticalComposition, the new controller's liveness depends on
    // other controllers' liveness
    proof fn liveness_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster, id: int, composed: Map<int, ControllerSpec>)
        requires
            (Self::c().membership)(cluster, id),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            spec.entails((Self::c().fairness)(id)),
            forall |other_id| #[trigger] cluster.controller_models.remove(id).contains_key(other_id)
                ==> spec.entails((Self::c().safety_partial_rely)(other_id)),
            forall |i| #[trigger] composed.contains_key(i)
                ==> spec.entails(composed[i].liveness_guarantee),
        ensures
            spec.entails(Self::c().liveness_guarantee),
        ;
}

proof fn horizontal_composition<HC>(spec: TempPred<ClusterState>, cluster: Cluster, id: int, composed: Map<int, ControllerSpec>)
    where
        HC: HorizontalComposition,
    requires
        !composed.contains_key(id),
        composable(spec, cluster, composed),
    ensures
        composable(spec, cluster, composed.insert(id, HC::c())),
{
    let composed = composed;
    let new_composed = composed.insert(id, HC::c());
    let others = cluster.controller_models.remove_keys(new_composed.dom());

    if (forall |i| #[trigger] new_composed.contains_key(i) ==> (new_composed[i].membership)(cluster, i))
        && spec.entails(lift_state(cluster.init()))
        && spec.entails(always(lift_action(cluster.next())))
    {
        assert((HC::c().membership)(cluster, id)) by {
            assert(new_composed.contains_key(id));
        }
        assert forall |i| #[trigger] composed.contains_key(i) implies (composed[i].membership)(cluster, i) by {
            assert(new_composed.contains_key(i));
        }

        HC::safety_is_guaranteed(spec, cluster, id);

        if (forall |i| #[trigger] new_composed.contains_key(i) ==> spec.entails((new_composed[i].fairness)(i)))
            && (forall |i| #[trigger] new_composed.contains_key(i) ==>
                    forall |j| #[trigger] others.contains_key(j) ==>
                        spec.entails((new_composed[i].safety_partial_rely)(j)))
        {
            HC::no_internal_interference(spec, cluster, id, composed);

            assert forall |i| #[trigger] composed.contains_key(i)
            implies spec.entails(composed[i].liveness_guarantee) by {
                assert forall |i| #[trigger] composed.contains_key(i) implies spec.entails((composed[i].fairness)(i)) by {
                    assert(new_composed.contains_key(i));
                }

                assert forall |i| #[trigger] composed.contains_key(i)
                implies (forall |j| #[trigger] cluster.controller_models.remove_keys(composed.dom()).contains_key(j)
                    ==> spec.entails((composed[i].safety_partial_rely)(j)))
                by {
                    assert(new_composed.contains_key(i));
                    assert forall |j| #[trigger] cluster.controller_models.remove_keys(composed.dom()).contains_key(j)
                    implies spec.entails((composed[i].safety_partial_rely)(j)) by {
                        if others.contains_key(j) {}
                    }
                }
            }

            assert(spec.entails(HC::c().liveness_guarantee)) by {
                assert(spec.entails((HC::c().fairness)(id))) by {
                    assert(new_composed.contains_key(id));
                }

                assert forall |other_id| #[trigger] cluster.controller_models.remove(id).contains_key(other_id)
                implies spec.entails((HC::c().safety_partial_rely)(other_id)) by {
                    if others.contains_key(other_id) {}
                }

                HC::liveness_is_guaranteed(spec, cluster, id);
            }
        }
    }
}

proof fn vertical_composition<VC>(spec: TempPred<ClusterState>, cluster: Cluster, id: int, composed: Map<int, ControllerSpec>)
    where
        VC: VerticalComposition,
    requires
        !composed.contains_key(id),
        composable(spec, cluster, composed),
    ensures
        composable(spec, cluster, composed.insert(id, VC::c())),
{
    let composed = composed;
    let new_composed = composed.insert(id, VC::c());
    let others = cluster.controller_models.remove_keys(new_composed.dom());

    if (forall |i| #[trigger] new_composed.contains_key(i) ==> (new_composed[i].membership)(cluster, i))
        && spec.entails(lift_state(cluster.init()))
        && spec.entails(always(lift_action(cluster.next())))
    {
        assert((VC::c().membership)(cluster, id)) by {
            assert(new_composed.contains_key(id));
        }
        assert forall |i| #[trigger] composed.contains_key(i) implies (composed[i].membership)(cluster, i) by {
            assert(new_composed.contains_key(i));
        }

        VC::safety_is_guaranteed(spec, cluster, id);

        if (forall |i| #[trigger] new_composed.contains_key(i) ==> spec.entails((new_composed[i].fairness)(i)))
            && (forall |i| #[trigger] new_composed.contains_key(i) ==>
                    forall |j| #[trigger] others.contains_key(j) ==>
                        spec.entails((new_composed[i].safety_partial_rely)(j)))
        {
            VC::no_internal_interference(spec, cluster, id, composed);

            assert forall |i| #[trigger] composed.contains_key(i)
            implies spec.entails(composed[i].liveness_guarantee) by {
                assert forall |i| #[trigger] composed.contains_key(i) implies spec.entails((composed[i].fairness)(i)) by {
                    assert(new_composed.contains_key(i));
                }

                assert forall |i| #[trigger] composed.contains_key(i)
                implies (forall |j| #[trigger] cluster.controller_models.remove_keys(composed.dom()).contains_key(j)
                    ==> spec.entails((composed[i].safety_partial_rely)(j)))
                by {
                    assert(new_composed.contains_key(i));
                    assert forall |j| #[trigger] cluster.controller_models.remove_keys(composed.dom()).contains_key(j)
                    implies spec.entails((composed[i].safety_partial_rely)(j)) by {
                        if others.contains_key(j) {}
                    }
                }
            }

            assert(spec.entails(VC::c().liveness_guarantee)) by {
                assert(spec.entails((VC::c().fairness)(id))) by {
                    assert(new_composed.contains_key(id));
                }

                assert forall |other_id| #[trigger] cluster.controller_models.remove(id).contains_key(other_id)
                implies spec.entails((VC::c().safety_partial_rely)(other_id)) by {
                    if others.contains_key(other_id) {}
                }

                VC::liveness_is_guaranteed(spec, cluster, id, composed);
            }
        }
    }
}

mod example {

use super::*;

// cook is a controller whose progress doesn't rely on other controllers

pub uninterp spec fn cook() -> ControllerSpec;

pub struct ComposeCook {}

impl Composition for ComposeCook {
    open spec fn c() -> ControllerSpec { cook() }

    #[verifier(external_body)]
    proof fn safety_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster, id: int) {}

    #[verifier(external_body)]
    proof fn no_internal_interference(spec: TempPred<ClusterState>, cluster: Cluster, id: int, composed: Map<int, ControllerSpec>) {}
}

impl HorizontalComposition for ComposeCook {
    #[verifier(external_body)]
    proof fn liveness_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster, id: int) {}
}

// waiter is a controller whose progress relies on cook's progress

pub uninterp spec fn waiter() -> ControllerSpec;

pub struct ComposeWaiter {}

impl Composition for ComposeWaiter {
    open spec fn c() -> ControllerSpec { waiter() }

    #[verifier(external_body)]
    proof fn safety_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster, id: int) {}

    #[verifier(external_body)]
    proof fn no_internal_interference(spec: TempPred<ClusterState>, cluster: Cluster, id: int, composed: Map<int, ControllerSpec>) {}
}

impl VerticalComposition for ComposeWaiter {
    #[verifier(external_body)]
    proof fn liveness_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster, id: int, composed: Map<int, ControllerSpec>) {}
}

// cook and waiter can be composed together

proof fn compose_cook_and_waiter(spec: TempPred<ClusterState>, cluster: Cluster, cook_id: int, waiter_id: int)
    requires
        cook_id != waiter_id,
    ensures
        composable(spec, cluster, Map::<int, ControllerSpec>::empty().insert(cook_id, cook()).insert(waiter_id, waiter()))
{
    let empty = Map::<int, ControllerSpec>::empty();
    horizontal_composition::<ComposeCook>(spec, cluster, cook_id, empty);
    vertical_composition::<ComposeWaiter>(spec, cluster, waiter_id, empty.insert(cook_id, cook()));
}

}

}
