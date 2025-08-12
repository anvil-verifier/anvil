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

    // The id of the controller we want to compose
    spec fn id() -> int;

    // The controllers that have been composed
    spec fn composed() -> Map<int, ControllerSpec>;

    // safety_guarantee of the new controller holds
    proof fn safety_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster)
        requires
            (Self::c().membership)(cluster, Self::id()),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
        ensures
            spec.entails(Self::c().safety_guarantee),
        ;

    // The new controller doesn't interfere with composed controllers, or
    // they satisfy each other's safety_partial_rely
    proof fn no_internal_interference(spec: TempPred<ClusterState>, cluster: Cluster)
        requires
            (Self::c().membership)(cluster, Self::id()),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            spec.entails(Self::c().safety_guarantee),
            !Self::composed().contains_key(Self::id()),
            forall |i| #[trigger] Self::composed().contains_key(i) ==> (Self::composed()[i].membership)(cluster, i),
            forall |i| #[trigger] Self::composed().contains_key(i) ==> spec.entails(Self::composed()[i].safety_guarantee),
        ensures
            forall |i| #[trigger] Self::composed().contains_key(i) ==>
                spec.entails((Self::c().safety_partial_rely)(i))
                && spec.entails((Self::composed()[i].safety_partial_rely)(Self::id()))
        ;
}

pub trait HorizontalComposition: Sized + Composition {
    // For HorizontalComposition, the new controller's liveness doesn't depend on
    // other controllers' liveness
    proof fn liveness_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster)
        requires
            (Self::c().membership)(cluster, Self::id()),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            spec.entails((Self::c().fairness)(Self::id())),
            forall |other_id| #[trigger] cluster.controller_models.remove(Self::id()).contains_key(other_id)
                ==> spec.entails((Self::c().safety_partial_rely)(other_id)),
        ensures
            spec.entails(Self::c().liveness_guarantee),
        ;
}

pub trait VerticalComposition: Sized + Composition {
    // For VerticalComposition, the new controller's liveness depends on
    // other controllers' liveness
    proof fn liveness_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster)
        requires
            (Self::c().membership)(cluster, Self::id()),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            spec.entails((Self::c().fairness)(Self::id())),
            forall |other_id| #[trigger] cluster.controller_models.remove(Self::id()).contains_key(other_id)
                ==> spec.entails((Self::c().safety_partial_rely)(other_id)),
            forall |i| #[trigger] Self::composed().contains_key(i)
                ==> spec.entails(Self::composed()[i].liveness_guarantee),
        ensures
            spec.entails(Self::c().liveness_guarantee),
        ;
}

proof fn horizontal_composition<HC>(spec: TempPred<ClusterState>, cluster: Cluster)
    where
        HC: HorizontalComposition,
    requires
        !HC::composed().contains_key(HC::id()),
        composable(spec, cluster, HC::composed()),
    ensures
        composable(spec, cluster, HC::composed().insert(HC::id(), HC::c())),
{
    let composed = HC::composed();
    let new_composed = HC::composed().insert(HC::id(), HC::c());
    let others = cluster.controller_models.remove_keys(new_composed.dom());

    if (forall |i| #[trigger] new_composed.contains_key(i) ==> (new_composed[i].membership)(cluster, i))
        && spec.entails(lift_state(cluster.init()))
        && spec.entails(always(lift_action(cluster.next())))
    {
        assert((HC::c().membership)(cluster, HC::id())) by {
            assert(new_composed.contains_key(HC::id()));
        }
        assert forall |i| #[trigger] composed.contains_key(i) implies (composed[i].membership)(cluster, i) by {
            assert(new_composed.contains_key(i));
        }

        HC::safety_is_guaranteed(spec, cluster);

        if (forall |i| #[trigger] new_composed.contains_key(i) ==> spec.entails((new_composed[i].fairness)(i)))
            && (forall |i| #[trigger] new_composed.contains_key(i) ==>
                    forall |j| #[trigger] others.contains_key(j) ==>
                        spec.entails((new_composed[i].safety_partial_rely)(j)))
        {
            HC::no_internal_interference(spec, cluster);

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
                assert(spec.entails((HC::c().fairness)(HC::id()))) by {
                    assert(new_composed.contains_key(HC::id()));
                }

                assert forall |other_id| #[trigger] cluster.controller_models.remove(HC::id()).contains_key(other_id)
                implies spec.entails((HC::c().safety_partial_rely)(other_id)) by {
                    if others.contains_key(other_id) {}
                }

                HC::liveness_is_guaranteed(spec, cluster);
            }
        }
    }
}

proof fn vertical_composition<VC>(spec: TempPred<ClusterState>, cluster: Cluster)
    where
        VC: VerticalComposition,
    requires
        !VC::composed().contains_key(VC::id()),
        composable(spec, cluster, VC::composed()),
    ensures
        composable(spec, cluster, VC::composed().insert(VC::id(), VC::c())),
{
    let composed = VC::composed();
    let new_composed = VC::composed().insert(VC::id(), VC::c());
    let others = cluster.controller_models.remove_keys(new_composed.dom());

    if (forall |i| #[trigger] new_composed.contains_key(i) ==> (new_composed[i].membership)(cluster, i))
        && spec.entails(lift_state(cluster.init()))
        && spec.entails(always(lift_action(cluster.next())))
    {
        assert((VC::c().membership)(cluster, VC::id())) by {
            assert(new_composed.contains_key(VC::id()));
        }
        assert forall |i| #[trigger] composed.contains_key(i) implies (composed[i].membership)(cluster, i) by {
            assert(new_composed.contains_key(i));
        }

        VC::safety_is_guaranteed(spec, cluster);

        if (forall |i| #[trigger] new_composed.contains_key(i) ==> spec.entails((new_composed[i].fairness)(i)))
            && (forall |i| #[trigger] new_composed.contains_key(i) ==>
                    forall |j| #[trigger] others.contains_key(j) ==>
                        spec.entails((new_composed[i].safety_partial_rely)(j)))
        {
            VC::no_internal_interference(spec, cluster);

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
                assert(spec.entails((VC::c().fairness)(VC::id()))) by {
                    assert(new_composed.contains_key(VC::id()));
                }

                assert forall |other_id| #[trigger] cluster.controller_models.remove(VC::id()).contains_key(other_id)
                implies spec.entails((VC::c().safety_partial_rely)(other_id)) by {
                    if others.contains_key(other_id) {}
                }

                VC::liveness_is_guaranteed(spec, cluster);
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

    uninterp spec fn id() -> int; // the actual value of id doesn't matter

    open spec fn composed() -> Map<int, ControllerSpec> { Map::<int, ControllerSpec>::empty() }

    #[verifier(external_body)]
    proof fn safety_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster) {}

    #[verifier(external_body)]
    proof fn no_internal_interference(spec: TempPred<ClusterState>, cluster: Cluster) {}
}

impl HorizontalComposition for ComposeCook {
    #[verifier(external_body)]
    proof fn liveness_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster) {}
}

// waiter is a controller whose progress relies on cook's progress

pub uninterp spec fn waiter() -> ControllerSpec;

pub struct ComposeWaiter {}

impl Composition for ComposeWaiter {
    open spec fn c() -> ControllerSpec { waiter() }

    uninterp spec fn id() -> int; // the actual value of id doesn't matter

    open spec fn composed() -> Map<int, ControllerSpec> { Map::<int, ControllerSpec>::empty().insert(ComposeCook::id(), cook()) }

    #[verifier(external_body)]
    proof fn safety_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster) {}

    #[verifier(external_body)]
    proof fn no_internal_interference(spec: TempPred<ClusterState>, cluster: Cluster) {}
}

impl VerticalComposition for ComposeWaiter {
    #[verifier(external_body)]
    proof fn liveness_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster) {}
}

// cook and waiter can be composed together

proof fn compose_cook_and_waiter(spec: TempPred<ClusterState>, cluster: Cluster)
    requires
        ComposeCook::id() != ComposeWaiter::id(),
    ensures
        composable(spec, cluster, Map::<int, ControllerSpec>::empty().insert(ComposeCook::id(), cook()).insert(ComposeWaiter::id(), waiter()))
{
    let empty = Map::<int, ControllerSpec>::empty();
    horizontal_composition::<ComposeCook>(spec, cluster);
    vertical_composition::<ComposeWaiter>(spec, cluster);
}

}

}
