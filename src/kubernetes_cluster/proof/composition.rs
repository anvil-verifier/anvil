use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::vstd_ext::map_lib::*;
use vstd::prelude::*;

verus! {

pub struct ControllerSpec {
    pub progress_guarantee: TempPred<ClusterState>,
    pub progress_rely: TempPred<ClusterState>,
    pub non_interference_guarantee: TempPred<ClusterState>,
    pub non_interference_partial_rely: spec_fn(int) -> TempPred<ClusterState>,
    pub fairness: TempPred<ClusterState>,
    pub membership: spec_fn(Cluster) -> bool,
}

pub open spec fn composable(spec: TempPred<ClusterState>, cluster: Cluster, controller_specs: Map<int, ControllerSpec>) -> bool {
    (
        forall_on_map(controller_specs, |i:int, c: ControllerSpec| (c.membership)(cluster))
        && spec.entails(lift_state(cluster.init()))
        && spec.entails(always(lift_action(cluster.next())))
        && forall_on_map(controller_specs, |i:int, c: ControllerSpec| spec.entails(c.fairness))
        && forall_on_map(controller_specs,
                |i:int, c: ControllerSpec| forall_on_map(cluster.controller_models.remove_keys(controller_specs.dom()),
                    |other, oc: ControllerModel| spec.entails((c.non_interference_partial_rely)(other)))
            )
    ) ==> (
        forall_on_map(controller_specs, |i:int, c: ControllerSpec| spec.entails(c.progress_guarantee))
        && forall_on_map(controller_specs, |i:int, c: ControllerSpec| spec.entails(c.non_interference_guarantee))
    )
}

#[verifier(external_body)]
proof fn horizontal_composition<HC>(spec: TempPred<ClusterState>, cluster: Cluster, id: int, c: ControllerSpec, composed: Map<int, ControllerSpec>)
    where
        HC: HorizontalComposition,
    requires
        composable(spec, cluster, HC::composed()),
    ensures
        composable(spec, cluster, HC::composed().insert(HC::id(), HC::c())),
{}

pub trait HorizontalComposition: Sized {
    spec fn id() -> int;

    spec fn c() -> ControllerSpec;

    spec fn composed() -> Map<int, ControllerSpec>;

    proof fn progress_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster)
        requires
            (Self::c().membership)(cluster),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            spec.entails(Self::c().fairness),
            forall |other_id| cluster.controller_models.remove(Self::id()).contains_key(other_id)
                ==> spec.entails((Self::c().non_interference_partial_rely)(other_id)),
        ensures
            spec.entails(Self::c().progress_guarantee),
        ;

    proof fn non_interference_is_guaranteed(spec: TempPred<ClusterState>, cluster: Cluster)
        requires
            (Self::c().membership)(cluster),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
        ensures
            spec.entails(Self::c().non_interference_guarantee),
        ;

    proof fn non_interference_is_compatible(spec: TempPred<ClusterState>, cluster: Cluster)
        requires
            (Self::c().membership)(cluster),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            spec.entails(Self::c().non_interference_guarantee),
            !Self::composed().contains_key(Self::id()),
            forall_on_map(Self::composed(), |i:int, c: ControllerSpec| (c.membership)(cluster)),
            forall_on_map(Self::composed(), |i:int, c: ControllerSpec| spec.entails(c.non_interference_guarantee)),
        ensures
            forall_on_map(Self::composed(), |i, c: ControllerSpec| spec.entails((Self::c().non_interference_partial_rely)(i))
                && spec.entails((c.non_interference_partial_rely)(Self::id())))
        ;
}

}