use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::vstd_ext::map_lib::*;
use vstd::prelude::*;

verus! {

pub struct ControllerSpec {
    pub liveness_guarantee: TempPred<ClusterState>,
    pub liveness_rely: TempPred<ClusterState>,
    pub safety_guarantee: TempPred<ClusterState>,
    pub safety_partial_rely: spec_fn(int) -> TempPred<ClusterState>,
    pub fairness: TempPred<ClusterState>,
    pub membership: spec_fn(Cluster) -> bool,
}

pub open spec fn composable(spec: TempPred<ClusterState>, cluster: Cluster, controller_specs: Map<int, ControllerSpec>) -> bool {
    &&& (forall |i| #[trigger] controller_specs.contains_key(i) ==> (controller_specs[i].membership)(cluster))
        && spec.entails(lift_state(cluster.init()))
        && spec.entails(always(lift_action(cluster.next())))
        ==> (forall |i| #[trigger] controller_specs.contains_key(i) ==> spec.entails(controller_specs[i].safety_guarantee))
    &&& (forall |i| #[trigger] controller_specs.contains_key(i) ==> (controller_specs[i].membership)(cluster))
        && spec.entails(lift_state(cluster.init()))
        && spec.entails(always(lift_action(cluster.next())))
        && (forall |i| #[trigger] controller_specs.contains_key(i) ==> spec.entails(controller_specs[i].fairness))
        && (forall |i| #[trigger] controller_specs.contains_key(i) ==>
            forall |j| #[trigger] cluster.controller_models.remove_keys(controller_specs.dom()).contains_key(j) ==>
                spec.entails((controller_specs[i].safety_partial_rely)(j)))
        ==> (forall |i| #[trigger] controller_specs.contains_key(i) ==> spec.entails(controller_specs[i].liveness_guarantee))
}

pub trait Composition: Sized {
    spec fn id() -> int;

    spec fn c() -> ControllerSpec;

    spec fn composed() -> Map<int, ControllerSpec>;

    proof fn safety_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster)
        requires
            (Self::c().membership)(cluster),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
        ensures
            spec.entails(Self::c().safety_guarantee),
        ;

    proof fn no_internal_interference(spec: TempPred<ClusterState>, cluster: Cluster)
        requires
            (Self::c().membership)(cluster),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            spec.entails(Self::c().safety_guarantee),
            !Self::composed().contains_key(Self::id()),
            forall |i| #[trigger] Self::composed().contains_key(i) ==> (Self::composed()[i].membership)(cluster),
            forall |i| #[trigger] Self::composed().contains_key(i) ==> spec.entails(Self::composed()[i].safety_guarantee),
        ensures
            forall |i| #[trigger] Self::composed().contains_key(i) ==>
                spec.entails((Self::c().safety_partial_rely)(i))
                && spec.entails((Self::composed()[i].safety_partial_rely)(Self::id()))
        ;
}

pub trait HorizontalComposition: Sized + Composition {
    proof fn liveness_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster)
        requires
            (Self::c().membership)(cluster),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            spec.entails(Self::c().fairness),
            forall |other_id| #[trigger] cluster.controller_models.remove(Self::id()).contains_key(other_id)
                ==> spec.entails((Self::c().safety_partial_rely)(other_id)),
        ensures
            spec.entails(Self::c().liveness_guarantee),
        ;
}

pub trait VerticalComposition: Sized + Composition {
    proof fn liveness_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster)
        requires
            (Self::c().membership)(cluster),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            spec.entails(Self::c().fairness),
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

    if (forall |i| #[trigger] new_composed.contains_key(i) ==> (new_composed[i].membership)(cluster))
        && spec.entails(lift_state(cluster.init()))
        && spec.entails(always(lift_action(cluster.next())))
    {
        assert((HC::c().membership)(cluster)) by {
            assert(new_composed.contains_key(HC::id()));
        }
        assert forall |i| #[trigger] composed.contains_key(i) implies (composed[i].membership)(cluster) by {
            assert(new_composed.contains_key(i));
        }
        
        HC::safety_is_guaranteed(spec, cluster);

        if (forall |i| #[trigger] new_composed.contains_key(i) ==> spec.entails(new_composed[i].fairness))
            && (forall |i| #[trigger] new_composed.contains_key(i) ==> 
                    forall |j| #[trigger] others.contains_key(j) ==>
                        spec.entails((new_composed[i].safety_partial_rely)(j)))
        {
            HC::no_internal_interference(spec, cluster);

            assert forall |i| #[trigger] composed.contains_key(i)
            implies spec.entails(composed[i].liveness_guarantee) by {
                assert forall |i| #[trigger] composed.contains_key(i) implies spec.entails(composed[i].fairness) by {
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
                assert(spec.entails(HC::c().fairness)) by {
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

    if (forall |i| #[trigger] new_composed.contains_key(i) ==> (new_composed[i].membership)(cluster))
        && spec.entails(lift_state(cluster.init()))
        && spec.entails(always(lift_action(cluster.next())))
    {
        assert((VC::c().membership)(cluster)) by {
            assert(new_composed.contains_key(VC::id()));
        }
        assert forall |i| #[trigger] composed.contains_key(i) implies (composed[i].membership)(cluster) by {
            assert(new_composed.contains_key(i));
        }
        
        VC::safety_is_guaranteed(spec, cluster);

        if (forall |i| #[trigger] new_composed.contains_key(i) ==> spec.entails(new_composed[i].fairness))
            && (forall |i| #[trigger] new_composed.contains_key(i) ==> 
                    forall |j| #[trigger] others.contains_key(j) ==>
                        spec.entails((new_composed[i].safety_partial_rely)(j)))
        {
            VC::no_internal_interference(spec, cluster);

            assert forall |i| #[trigger] composed.contains_key(i)
            implies spec.entails(composed[i].liveness_guarantee) by {
                assert forall |i| #[trigger] composed.contains_key(i) implies spec.entails(composed[i].fairness) by {
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
                assert(spec.entails(VC::c().fairness)) by {
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

}
