use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::trusted::liveness_theorem as vrs_liveness;
use crate::vdeployment_controller::trusted::liveness_theorem as vd_liveness;
use crate::vreplicaset_controller::trusted::{
    spec_types::*, rely_guarantee::*
};
use crate::vreplicaset_controller::model::reconciler::VReplicaSetReconciler;
use crate::composition::vreplicaset_reconciler::*;
use crate::vdeployment_controller::trusted::{
    spec_types::*, rely_guarantee::*, util::*
};
use crate::vdeployment_controller::model::{
    reconciler::*, install::*
};
use crate::vdeployment_controller::proof::{
    guarantee::*, liveness::{spec::*, proof::*}, predicate::*
};
use crate::vstd_ext::{
    string_view::*, seq_lib::*
};
use vstd::prelude::*;

verus !{


impl Composition for VDeploymentReconciler {
    open spec fn c() -> ControllerSpec {
        ControllerSpec{
            liveness_guarantee: composed_vd_eventually_stable_reconciliation(),
            liveness_rely: vrs_liveness::vrs_eventually_stable_reconciliation(),
            safety_guarantee: always(lift_state(vd_guarantee(Self::id()))),
            safety_partial_rely: |other_id: int| always(lift_state(vd_rely(other_id))),
            fairness: |cluster: Cluster| next_with_wf(cluster, Self::id()),
            membership: |cluster: Cluster, id: int| {
                &&& cluster.controller_models.contains_pair(id, vd_controller_model())
                &&& cluster.type_is_installed_in_cluster::<VDeploymentView>()
                &&& cluster.type_is_installed_in_cluster::<VReplicaSetView>()
            },
        }
    }

    uninterp spec fn id() -> int;

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
    proof fn liveness_guarantee_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().liveness_guarantee),
    {
        eventually_stable_reconciliation_holds(spec, cluster, Self::id());
        composed_eventually_stable_reconciliation_holds(spec);
    }

    proof fn liveness_rely_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().liveness_rely),
    {
        assert(Self::composed().contains_key(VReplicaSetReconciler::id())); // trigger
    }
}

//* ESR composition *//

pub open spec fn composed_vd_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    tla_forall(composed_vd_eventually_stable_reconciliation_per_cr())
}

// TODO: only talk about vd
pub open spec fn composed_vd_eventually_stable_reconciliation_per_cr() -> spec_fn(VDeploymentView) -> TempPred<ClusterState> {
    |vd: VDeploymentView| always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(current_pods_match(vd))))
}

pub open spec fn current_pods_match(vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.resources().values().filter(valid_owned_pods(vd, s)).len() == vd.spec.replicas.unwrap_or(1)
    }
}

pub open spec fn valid_owned_pods(vd: VDeploymentView, s: ClusterState) -> spec_fn(DynamicObjectView) -> bool {
    |obj: DynamicObjectView| {
        &&& s.resources().values().contains(obj)
        &&& exists |vrs: VReplicaSetView| {
            &&& #[trigger] vrs_liveness::owned_selector_match_is(vrs, obj)
            &&& valid_owned_vrs(vrs, vd)
            &&& s.resources().contains_key(vrs.object_ref())
            &&& VReplicaSetView::unmarshal(s.resources()[vrs.object_ref()]) is Ok
            &&& VReplicaSetView::unmarshal(s.resources()[vrs.object_ref()])->Ok_0 == vrs
        }
    }
}

// TODO: deprecate this
pub open spec fn valid_owned_vrs_p(vrs: VReplicaSetView, vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let etcd_obj = s.resources()[vrs.object_ref()];
        let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
        &&& s.resources().contains_key(vrs.object_ref())
        &&& VReplicaSetView::unmarshal(etcd_obj) is Ok
        &&& etcd_vrs == vrs
        &&& valid_owned_vrs(etcd_vrs, vd)
    }
}

// TODO: find a way to weaken this
// maybe "there does not exist a vrs that has non-zero replcias and belongs to vd not included in this set"
pub open spec fn vrs_set_matches_vd(vrs_set: Set<VReplicaSetView>, vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| vrs_set == s.resources().values()
        .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
        .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
        .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd))
}

pub open spec fn current_state_matches_vrs_set_for_vd(vrs_set: Set<VReplicaSetView>, vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        // interpret current_state_matches using vrs_set
        // there only exists one up-to-date vrs has matching replicas
        // and other owned vrs has 0 replicas
        &&& exists |vrs: VReplicaSetView| {
            &&& #[trigger] vrs_set.contains(vrs)
            &&& s.resources().values().contains(vrs.marshal())
            &&& valid_owned_vrs(vrs, vd)
            &&& vrs.spec.replicas.unwrap_or(1) == vd.spec.replicas.unwrap_or(1) // vd.spec.replicas can be Some(0)
            // no old vrs, including the 2nd new vrs (if any)
            &&& !exists |old_vrs: VReplicaSetView| {
                &&& #[trigger] vrs_set.contains(old_vrs)
                &&& old_vrs != vrs
                &&& s.resources().values().contains(old_vrs.marshal())
                &&& valid_owned_vrs(old_vrs, vd)
                &&& old_vrs.spec.replicas.unwrap_or(1) > 0 // != Some(0)
            }
        }
    }
}

// verus didn't recognize inline closure directly
pub open spec fn desired_state_is_vrs() -> spec_fn(VReplicaSetView) -> StatePred<ClusterState> {
    |vrs: VReplicaSetView| Cluster::desired_state_is(vrs)
}

pub open spec fn current_state_matches_vrs() -> spec_fn(VReplicaSetView) -> StatePred<ClusterState> {
    |vrs: VReplicaSetView| vrs_liveness::current_state_matches(vrs)
}

pub open spec fn conjuncted_desired_state_is_vrs(vrs_set: Set<VReplicaSetView>) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |vrs| #[trigger] vrs_set.contains(vrs) ==> Cluster::desired_state_is(vrs)(s)
    }
}

pub open spec fn lifted_conjuncted_desired_state_is_vrs(vrs_set: Set<VReplicaSetView>) -> spec_fn(VReplicaSetView) -> TempPred<ClusterState> {
    |vrs: VReplicaSetView| lift_state(|s: ClusterState| vrs_set.contains(vrs) ==> Cluster::desired_state_is(vrs)(s))
}

pub open spec fn lifted_conjuncted_current_state_matches_vrs(vrs_set: Set<VReplicaSetView>) -> spec_fn(VReplicaSetView) -> TempPred<ClusterState> {
    |vrs: VReplicaSetView| lift_state(|s: ClusterState| vrs_set.contains(vrs) ==> vrs_liveness::current_state_matches(vrs)(s))
}

pub proof fn vrs_set_matches_vd_stable_state_leads_to_current_pods_match_vd(spec: TempPred<ClusterState>, vrs_set: Set<VReplicaSetView>, vd: VDeploymentView)
requires
    // VRS ESR
    vrs_set.finite(),
    vrs_set.len() > 0,
    spec.entails(tla_forall(|vrs| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))))),
ensures
    spec.entails(always(
        lift_state(vrs_set_matches_vd(vrs_set, vd))
        .and(lift_state(current_state_matches_vrs_set_for_vd(vrs_set, vd)))
        .and(tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set))))
        .leads_to(always(lift_state(current_pods_match(vd))))),
{
    // q1 ~> q2 ==>
    // [](q & q & r) ~> [](p & q2 & r)
    always_and_equality(
        lift_state(vrs_set_matches_vd(vrs_set, vd)).and(lift_state(current_state_matches_vrs_set_for_vd(vrs_set, vd))),
        tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set))
    );
    assert(spec.entails(always(tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set))).leads_to(always(tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set)))))) by {
        assert forall |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs) implies
            spec.entails(always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs))))) by {
            use_tla_forall(spec, |vrs| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))), vrs);
        }
        assert(spec.entails(always(tla_forall(|vrs: VReplicaSetView| lift_state(|s: ClusterState| #[trigger] vrs_set.contains(vrs) ==> desired_state_is_vrs()(vrs)(s))))
            .leads_to(always(tla_forall(|vrs: VReplicaSetView| lift_state(|s: ClusterState| #[trigger] vrs_set.contains(vrs) ==> current_state_matches_vrs()(vrs)(s))))))) by {
            spec_entails_always_tla_forall_leads_to_always_tla_forall_within_domain(spec, desired_state_is_vrs(), current_state_matches_vrs(), vrs_set);
        }
        // flaky
        assume(tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set)).entails(tla_forall(|vrs: VReplicaSetView| lift_state(|s: ClusterState| #[trigger] vrs_set.contains(vrs) ==> desired_state_is_vrs()(vrs)(s)))));
        assume(tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set)).entails(tla_forall(|vrs: VReplicaSetView| lift_state(|s: ClusterState| #[trigger] vrs_set.contains(vrs) ==> current_state_matches_vrs()(vrs)(s)))));
        assume(tla_forall(|vrs: VReplicaSetView| lift_state(|s: ClusterState| #[trigger] vrs_set.contains(vrs) ==> desired_state_is_vrs()(vrs)(s))).entails(tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set))));
        assume(tla_forall(|vrs: VReplicaSetView| lift_state(|s: ClusterState| #[trigger] vrs_set.contains(vrs) ==> current_state_matches_vrs()(vrs)(s))).entails(tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set))));
        temp_pred_equality(tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set)), tla_forall(|vrs: VReplicaSetView| lift_state(|s: ClusterState| #[trigger] vrs_set.contains(vrs) ==> desired_state_is_vrs()(vrs)(s))));
        temp_pred_equality(tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set)), tla_forall(|vrs: VReplicaSetView| lift_state(|s: ClusterState| #[trigger] vrs_set.contains(vrs) ==> current_state_matches_vrs()(vrs)(s))));
    }
    // TODO: simplify using leads_to_always_combine
    leads_to_self_temp(always(lift_state(vrs_set_matches_vd(vrs_set, vd)).and(lift_state(current_state_matches_vrs_set_for_vd(vrs_set, vd)))));
    always_leads_to_always_combine(spec,
        lift_state(vrs_set_matches_vd(vrs_set, vd)).and(lift_state(current_state_matches_vrs_set_for_vd(vrs_set, vd))),
        tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set)),
        lift_state(vrs_set_matches_vd(vrs_set, vd)).and(lift_state(current_state_matches_vrs_set_for_vd(vrs_set, vd))),
        tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set))
    );
    assert(always(lift_state(vrs_set_matches_vd(vrs_set, vd)).and(lift_state(current_state_matches_vrs_set_for_vd(vrs_set, vd))).and(tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set)))).entails(
        always(lift_state(current_pods_match(vd))))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(vrs_set_matches_vd(vrs_set, vd)).and(lift_state(current_state_matches_vrs_set_for_vd(vrs_set, vd))).and(tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set))).satisfied_by(ex)
            implies #[trigger] lift_state(current_pods_match(vd)).satisfied_by(ex) by {
            assert(forall |vrs| #[trigger] vrs_set.contains(vrs) ==> vrs_liveness::current_state_matches(vrs)(ex.head())) by {
                assert(forall |vrs| #![trigger vrs_set.contains(vrs)] lifted_conjuncted_current_state_matches_vrs(vrs_set)(vrs).satisfied_by(ex));
            }
            current_state_match_combining_vrs_vd(vrs_set, vd, ex.head());
        }
        entails_preserved_by_always(
            lift_state(vrs_set_matches_vd(vrs_set, vd)).and(lift_state(current_state_matches_vrs_set_for_vd(vrs_set, vd))).and(tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set))),
            lift_state(current_pods_match(vd))
        );
    }
    entails_implies_leads_to(spec,
        always(lift_state(vrs_set_matches_vd(vrs_set, vd)).and(lift_state(current_state_matches_vrs_set_for_vd(vrs_set, vd))).and(tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set)))),
        always(lift_state(current_pods_match(vd)))
    );
    leads_to_trans(spec,
        always(lift_state(vrs_set_matches_vd(vrs_set, vd)).and(lift_state(current_state_matches_vrs_set_for_vd(vrs_set, vd))).and(tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set)))),
        always(lift_state(vrs_set_matches_vd(vrs_set, vd)).and(lift_state(current_state_matches_vrs_set_for_vd(vrs_set, vd))).and(tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set)))),
        always(lift_state(current_pods_match(vd)))
    );
}

pub proof fn pods_match_vrs_set(vrs_set: Set<VReplicaSetView>, s: ClusterState)
requires
    forall |vrs| #[trigger] vrs_set.contains(vrs) ==> vrs_liveness::current_state_matches(vrs)(s),
ensures
    s.resources().values().filter(|obj: DynamicObjectView| exists |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs) && #[trigger] vrs_liveness::owned_selector_match_is(vrs, obj)).len()
        == sum(vrs_set.to_seq().map_values(|vrs: VReplicaSetView| vrs.spec.replicas.unwrap_or(int1!())))
{}


pub proof fn current_state_match_combining_vrs_vd(vrs_set: Set<VReplicaSetView>, vd: VDeploymentView, s: ClusterState)
requires
    vrs_set_matches_vd(vrs_set, vd)(s),
    forall |vrs| #[trigger] vrs_set.contains(vrs) ==> vrs_liveness::current_state_matches(vrs)(s),
    current_state_matches_vrs_set_for_vd(vrs_set, vd)(s),
ensures
    current_pods_match(vd)(s),
{}

#[verifier(external_body)]
pub proof fn current_state_match_vd_implies_exists_vrs_set_with_desired_state_is(vd: VDeploymentView)
ensures
    lift_state(vd_liveness::current_state_matches(vd)).entails(
    tla_exists(|vrs_set: Set<VReplicaSetView>|
        lift_state(vrs_set_matches_vd(vrs_set, vd))
        .and(lift_state(current_state_matches_vrs_set_for_vd(vrs_set, vd)))
        .and(tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set)))
    )),
{}

pub proof fn lemma_always_current_state_match_vd_entails_exists_vrs_set_always_desired_state_is(vd: VDeploymentView)
requires
    true, // cluster invariants
ensures
    always(lift_state(vd_liveness::current_state_matches(vd))).entails( // try proving equivlance
    tla_exists(|vrs_set: Set<VReplicaSetView>| always( // or go with the hard way
        lift_state(vrs_set_matches_vd(vrs_set, vd))
        .and(lift_state(current_state_matches_vrs_set_for_vd(vrs_set, vd)))
        .and(tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set))
    )))),
{}

#[verifier(external_body)] // similar to current_state_match_combining_vrs_vd but need to prove stability
pub proof fn composed_desired_state_is_stable(
    vd: VDeploymentView, cluster: Cluster, vrs_set: Set<VReplicaSetView>, s: ClusterState, s_prime: ClusterState
)
requires
    cluster.next()(s, s_prime),
    vd_liveness::current_state_matches(vd)(s),
    vrs_set_matches_vd(vrs_set, vd)(s),
    current_state_matches_vrs_set_for_vd(vrs_set, vd)(s),
    forall |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs) ==> Cluster::desired_state_is(vrs)(s),
ensures
    vd_liveness::current_state_matches(vd)(s_prime),
    vrs_set_matches_vd(vrs_set, vd)(s_prime),
    current_state_matches_vrs_set_for_vd(vrs_set, vd)(s_prime),
    forall |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs) ==> Cluster::desired_state_is(vrs)(s_prime),
{}

pub proof fn composed_eventually_stable_reconciliation_holds(spec: TempPred<ClusterState>)
requires
    spec.entails(vrs_liveness::vrs_eventually_stable_reconciliation()),
    spec.entails(vd_liveness::vd_eventually_stable_reconciliation()),
ensures
    spec.entails(composed_vd_eventually_stable_reconciliation()),
{
    // unwrap, flaky
    assume(vrs_liveness::vrs_eventually_stable_reconciliation().entails(
        tla_forall(|vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))))));
    assume(tla_forall(|vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs))))).entails(
        vrs_liveness::vrs_eventually_stable_reconciliation()));
    temp_pred_equality(vrs_liveness::vrs_eventually_stable_reconciliation(),
        tla_forall(|vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs))))));
    assert forall |vrs| #[trigger] spec.entails(always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs))))) by {
        use_tla_forall(spec, |vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))), vrs);
    }
    assume(vd_liveness::vd_eventually_stable_reconciliation().entails(
        tla_forall(|vd: VDeploymentView| always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(vd_liveness::current_state_matches(vd)))))));
    assume(tla_forall(|vd: VDeploymentView| always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(vd_liveness::current_state_matches(vd))))).entails(
        vd_liveness::vd_eventually_stable_reconciliation()));
    temp_pred_equality(vd_liveness::vd_eventually_stable_reconciliation(),
        tla_forall(|vd: VDeploymentView| always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(vd_liveness::current_state_matches(vd))))));
    assert forall |vd: VDeploymentView| #[trigger] spec.entails(always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(vd_liveness::current_state_matches(vd))))) by {
        use_tla_forall(spec, |vd: VDeploymentView| always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(vd_liveness::current_state_matches(vd)))), vd);
    }
    
    assert forall |vd: VDeploymentView| #[trigger] spec.entails(composed_vd_eventually_stable_reconciliation_per_cr()(vd)) by {
        let always_desired_state_is_vrs_set = |vrs_set: Set<VReplicaSetView>|
            always(lift_state(vrs_set_matches_vd(vrs_set, vd))
            .and(lift_state(current_state_matches_vrs_set_for_vd(vrs_set, vd)))
            .and(tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set))));
            // tla_forall(|vrs: VReplicaSetView| crashes verus
        lemma_always_current_state_match_vd_entails_exists_vrs_set_always_desired_state_is(vd);
        entails_implies_leads_to(spec, always(lift_state(vd_liveness::current_state_matches(vd))), tla_exists(always_desired_state_is_vrs_set));
        assert forall |vrs_set: Set<VReplicaSetView>| #[trigger] spec.entails(always_desired_state_is_vrs_set(vrs_set).leads_to(always(lift_state(current_pods_match(vd))))) by {
            assume(vrs_set.finite());
            assume(vrs_set.len() > 0);
            vrs_set_matches_vd_stable_state_leads_to_current_pods_match_vd(spec, vrs_set, vd);
        }
        leads_to_exists_intro(spec, always_desired_state_is_vrs_set, always(lift_state(current_pods_match(vd))));
        leads_to_trans_n!(spec,
            always(lift_state(vd_liveness::desired_state_is(vd))),
            always(lift_state(vd_liveness::current_state_matches(vd))),
            tla_exists(always_desired_state_is_vrs_set),
            always(lift_state(current_pods_match(vd)))
        );
        temp_pred_equality(
            composed_vd_eventually_stable_reconciliation_per_cr()(vd),
            always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(current_pods_match(vd))))
        );
    }

    spec_entails_tla_forall(spec, composed_vd_eventually_stable_reconciliation_per_cr());
}

}