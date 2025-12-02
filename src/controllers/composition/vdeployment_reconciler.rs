use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::{
    cluster::*, message::*
};
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
    guarantee::*, liveness::{spec::*, proof::*}, predicate::*, helper_lemmas::*, helper_invariants, liveness::api_actions::*
};
use crate::vdeployment_controller::proof::liveness::resource_match::lemma_esr_preserves_from_s_to_s_prime;
use crate::vstd_ext::{
    string_view::*, seq_lib::*, set_lib::*, map_lib::*
};
use vstd::{
    prelude::*, set_lib::*
};

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
        assume(vrs_liveness::vrs_eventually_stable_reconciliation() ==
            tla_forall(|vrs: VReplicaSetView| always(lift_state(desired_state_is_vrs()(vrs))).leads_to(always(lift_state(current_state_matches_vrs()(vrs))))));
        assume(vd_liveness::vd_eventually_stable_reconciliation() ==
            tla_forall(|vd: VDeploymentView| always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(vd_liveness::current_state_matches(vd))))));
        assert forall |vrs| #[trigger] spec.entails(always(lift_state(desired_state_is_vrs()(vrs))).leads_to(always(lift_state(current_state_matches_vrs()(vrs))))) by {
            use_tla_forall(spec, |vrs: VReplicaSetView| always(lift_state(desired_state_is_vrs()(vrs))).leads_to(always(lift_state(current_state_matches_vrs()(vrs)))), vrs);
        }
        assert forall |vd: VDeploymentView| #[trigger] spec.entails(always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(vd_liveness::current_state_matches(vd))))) by {
            use_tla_forall(spec, |vd: VDeploymentView| always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(vd_liveness::current_state_matches(vd)))), vd);
        }
        assert forall |vd| #[trigger] spec.entails(always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(current_pods_match(vd))))) by {
            // TODO: rework liveness/proof.rs to have spec_entails_assumption_and_invariants_of_all_phases
            assume(spec.entails(assumption_and_invariants_of_all_phases(vd, cluster, Self::id())));
            // TODO: import reachability proof of stronger_esr
            assume(spec.entails(always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(lift_state(stronger_esr(vd, Self::id())))));
            assume(spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, Self::id())))));
            assume(spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(Self::id()))));
            vrs_set_matches_vd_stable_state_leads_to_current_pods_match_vd(spec, vd, Self::id(), cluster);
        }
        spec_entails_tla_forall(spec, |vd| always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(current_pods_match(vd)))));
        assume(composed_vd_eventually_stable_reconciliation() ==
            tla_forall(|vd| always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(current_pods_match(vd))))));
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
            &&& VReplicaSetView::unmarshal(s.resources()[vrs.object_ref()])->Ok_0 == vrs
        }
    }
}

// *** ESR composition helpers ***
// verus didn't recognize inline closure directly, so we use nested(3-fold) spec_fn here
pub open spec fn desired_state_is_vrs() -> spec_fn(VReplicaSetView) -> StatePred<ClusterState> {
    |vrs: VReplicaSetView| Cluster::desired_state_is(vrs)
}

pub open spec fn current_state_matches_vrs() -> spec_fn(VReplicaSetView) -> StatePred<ClusterState> {
    |vrs: VReplicaSetView| vrs_liveness::current_state_matches(vrs)
}

pub open spec fn conjuncted_desired_state_is_vrs(vrs_set: Set<VReplicaSetView>) -> StatePred<ClusterState> {
    |s: ClusterState| (forall |vrs| #[trigger] vrs_set.contains(vrs) ==> desired_state_is_vrs()(vrs)(s))
}

pub open spec fn lifted_conjuncted_desired_state_is_vrs(vrs_set: Set<VReplicaSetView>) -> spec_fn(VReplicaSetView) -> TempPred<ClusterState> {
    |vrs: VReplicaSetView| lift_state(|s: ClusterState| vrs_set.contains(vrs) ==> desired_state_is_vrs()(vrs)(s))
}

pub open spec fn conjuncted_current_state_matches_vrs(vrs_set: Set<VReplicaSetView>) -> StatePred<ClusterState> {
    |s: ClusterState| (forall |vrs| #[trigger] vrs_set.contains(vrs) ==> current_state_matches_vrs()(vrs)(s))
}

pub open spec fn lifted_conjuncted_current_state_matches_vrs(vrs_set: Set<VReplicaSetView>) -> spec_fn(VReplicaSetView) -> TempPred<ClusterState> {
    |vrs: VReplicaSetView| lift_state(|s: ClusterState| vrs_set.contains(vrs) ==> current_state_matches_vrs()(vrs)(s))
}

#[verifier(external_body)]
pub proof fn conjuncted_desired_state_is_vrs_equiv_lifted(vrs_set: Set<VReplicaSetView>)
ensures
    lift_state(conjuncted_desired_state_is_vrs(vrs_set)) == tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set)),
{}

#[verifier(external_body)]
pub proof fn conjuncted_current_state_matches_vrs_equiv_lifted(vrs_set: Set<VReplicaSetView>)
ensures
    lift_state(conjuncted_current_state_matches_vrs(vrs_set)) == tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set)),
{}

pub open spec fn current_state_match_vd_applied_to_vrs_set(vrs_set: Set<VReplicaSetView>, vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& vrs_set == s.resources().values()
            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
            .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd))
        &&& exists |vrs: VReplicaSetView| {
            &&& #[trigger] vrs_set.contains(vrs)
            &&& vrs.spec.replicas.unwrap_or(1) == vd.spec.replicas.unwrap_or(1) // vd.spec.replicas can be Some(0)
            &&& match_template_without_hash(vd.spec.template)(vrs)
            // no old vrs, including the 2nd new vrs (if any)
            &&& !exists |old_vrs: VReplicaSetView| {
                &&& #[trigger] vrs_set.contains(old_vrs)
                &&& old_vrs != vrs
                &&& old_vrs.spec.replicas.unwrap_or(1) > 0 // != Some(0)
            }
        }
    }
}

// ESR vertical composition
pub proof fn vrs_set_matches_vd_stable_state_leads_to_current_pods_match_vd(spec: TempPred<ClusterState>, vd: VDeploymentView, controller_id: int, cluster: Cluster)
requires
    // environment invariants
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
        ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    // lifted_vd_post
    spec.entails(always(lift_action(cluster.next()))),
    // ESR for vrs
    spec.entails(tla_forall(|vrs| always(lift_state(desired_state_is_vrs()(vrs))).leads_to(always(lift_state(current_state_matches_vrs()(vrs)))))),
    // ESR for vd, note: stability is not required
    spec.entails(always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(lift_state(stronger_esr(vd, controller_id)))),
ensures
    spec.entails(always(lift_state(vd_liveness::desired_state_is(vd))).leads_to(always(lift_state(current_pods_match(vd))))),
{
    let lifted_inv = lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
        .and(later(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))));
    let lifted_always_vd_pre = always(lift_state(vd_liveness::desired_state_is(vd)));
    let lifted_vd_post = lift_state(stronger_esr(vd, controller_id));
    let vrs_set_pre = |vrs_set| and!(
        current_state_match_vd_applied_to_vrs_set(vrs_set, vd),
        conjuncted_desired_state_is_vrs(vrs_set)
    );
    let vd_post_and_vrs_set_pre = |vrs_set| and!(
        stronger_esr(vd, controller_id),
        current_state_match_vd_applied_to_vrs_set(vrs_set, vd),
        conjuncted_desired_state_is_vrs(vrs_set)
    );
    let lifted_always_vrs_set_pre = |vrs_set| always(
        lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd))
        .and(tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set)))
    );
    let lifted_always_vrs_set_post = |vrs_set| always(
        lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd))
        .and(tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set)))
    );
    let lifted_always_composed_post = always(lift_state(current_pods_match(vd)));
    assert(spec.entails(always(lifted_inv))) by {
        always_to_always_later(spec, lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)));
        entails_always_and_n!(spec, 
            lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
            later(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))
        );
        temp_pred_equality(
            lifted_inv,
            lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
                .and(later(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
        );
    }
    assert(spec.entails(lifted_vd_post.leads_to(tla_exists(lifted_always_vrs_set_pre)))) by {
        assert(tla_exists(lifted_always_vrs_set_pre) == tla_exists(|vrs_set| always(lift_state(vrs_set_pre(vrs_set))))) by {
            // get rid of closure
            assert forall |vrs_set| #[trigger] lifted_always_vrs_set_pre(vrs_set) == always(lift_state(vrs_set_pre(vrs_set))) by {
                conjuncted_desired_state_is_vrs_equiv_lifted(vrs_set);
                and_eq(current_state_match_vd_applied_to_vrs_set(vrs_set, vd), conjuncted_desired_state_is_vrs(vrs_set));
                temp_pred_equality(lifted_always_vrs_set_pre(vrs_set), always(lift_state(vrs_set_pre(vrs_set))));
            }
            tla_exists_p_tla_exists_q_equality(lifted_always_vrs_set_pre, |vrs_set| always(lift_state(vrs_set_pre(vrs_set))));
        }
        assert(spec.entails(lifted_vd_post.leads_to(tla_exists(lifted_always_vrs_set_pre)))) by {
            assert(spec.entails(lifted_vd_post.leads_to(tla_exists(|vrs_set: Set<VReplicaSetView>| lift_state(vd_post_and_vrs_set_pre(vrs_set)))))) by {
                assert(lifted_vd_post.and(lifted_inv).entails(tla_exists(|vrs_set: Set<VReplicaSetView>| lift_state(vd_post_and_vrs_set_pre(vrs_set))))) by {
                    assert forall |ex: Execution<ClusterState>| #[trigger] lifted_vd_post.and(lifted_inv).satisfied_by(ex) implies
                        tla_exists(|vrs_set: Set<VReplicaSetView>| lift_state(vd_post_and_vrs_set_pre(vrs_set))).satisfied_by(ex) by {
                        let vrs_set = current_state_match_vd_implies_exists_vrs_set_with_desired_state_is(vd, cluster, controller_id, ex.head());
                        assert((|vrs_set: Set<VReplicaSetView>| lift_state(vd_post_and_vrs_set_pre(vrs_set)))(vrs_set).satisfied_by(ex));
                    }
                }
                entails_implies_leads_to(spec, lifted_vd_post.and(lifted_inv), tla_exists(|vrs_set: Set<VReplicaSetView>| lift_state(vd_post_and_vrs_set_pre(vrs_set))));
                leads_to_by_borrowing_inv(spec, lifted_vd_post, tla_exists(|vrs_set: Set<VReplicaSetView>| lift_state(vd_post_and_vrs_set_pre(vrs_set))), lifted_inv);
            }
            let stronger_next = |s, s_prime| {
                &&& cluster.next()(s, s_prime)
                &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
                &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime)
                &&& forall |vd: VDeploymentView| #[trigger] helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
                &&& vd_rely_condition(cluster, controller_id)(s)
            };
            helper_invariants::lemma_spec_entails_lifted_cluster_invariants_since_reconciliation(spec, vd, cluster, controller_id);
            vd_rely_condition_equivalent_to_lifted_vd_rely_condition(spec, cluster, controller_id);
            always_to_always_later(spec, lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)));
            combine_spec_entails_always_n!(spec,
                lift_action(stronger_next),
                lift_action(cluster.next()),
                lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
                lifted_vd_rely_condition(cluster, controller_id),
                lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
                later(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))
            );
            // vd_post_and_vrs_set_pre is stable
            assert forall |s, s_prime| true implies (forall |vrs_set| #[trigger] vd_post_and_vrs_set_pre(vrs_set)(s) && #[trigger] stronger_next(s, s_prime) ==> vd_post_and_vrs_set_pre(vrs_set)(s_prime)) by {
                assert forall |vrs_set| #[trigger] vd_post_and_vrs_set_pre(vrs_set)(s) && stronger_next(s, s_prime) implies vd_post_and_vrs_set_pre(vrs_set)(s_prime) by {
                    composed_desired_state_is_stable(vd, controller_id, cluster, vrs_set, s, s_prime);
                }
            }
            // lifted_vd_post ~> \E|vrs_set| []vd_post_and_vrs_set_pre
            leads_to_exists_stable(spec, stronger_next, lifted_vd_post, vd_post_and_vrs_set_pre);
            assert forall |vrs_set: Set<VReplicaSetView>| #[trigger] spec.entails(always(lift_state(vd_post_and_vrs_set_pre(vrs_set))).leads_to(always(lift_state(vrs_set_pre(vrs_set))))) by {
                always_weaken(always(lift_state(vd_post_and_vrs_set_pre(vrs_set))), lift_state(vd_post_and_vrs_set_pre(vrs_set)), lift_state(vrs_set_pre(vrs_set)));
                entails_implies_leads_to(spec, always(lift_state(vd_post_and_vrs_set_pre(vrs_set))), always(lift_state(vrs_set_pre(vrs_set))));
            }
            leads_to_exists_intro2(spec, |vrs_set: Set<VReplicaSetView>| always(lift_state(vd_post_and_vrs_set_pre(vrs_set))), |vrs_set: Set<VReplicaSetView>| always(lift_state(vrs_set_pre(vrs_set))));
            temp_pred_equality(tla_exists(|vrs_set: Set<VReplicaSetView>| always(lift_state(vrs_set_pre(vrs_set)))), tla_exists(lifted_always_vrs_set_pre));
            leads_to_trans(spec, lifted_vd_post, tla_exists(|vrs_set: Set<VReplicaSetView>| always(lift_state(vd_post_and_vrs_set_pre(vrs_set)))), tla_exists(lifted_always_vrs_set_pre));
        }
    }
    assert forall |vrs_set| #[trigger] spec.entails(lifted_always_vrs_set_pre(vrs_set).leads_to(lifted_always_composed_post)) by {
        assume(vrs_set.finite() && vrs_set.len() > 0); // a bit hacky
        // q1 ~> q2 ==>
        // [](q & q & r) ~> [](p & q2 & r)
        always_and_equality(
            lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)),
            tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set))
        );
        assert(spec.entails(always(tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set))).leads_to(always(tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set)))))) by {
            assert forall |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs) implies
                spec.entails(always(lift_state(desired_state_is_vrs()(vrs))).leads_to(always(lift_state(current_state_matches_vrs()(vrs))))) by {
                use_tla_forall(spec, |vrs| always(lift_state(desired_state_is_vrs()(vrs))).leads_to(always(lift_state(current_state_matches_vrs()(vrs)))), vrs);
            }
            assert(spec.entails(always(tla_forall(|vrs| lift_state(|s: ClusterState| vrs_set.contains(vrs) ==> desired_state_is_vrs()(vrs)(s))))
                .leads_to(always(tla_forall(|vrs| lift_state(|s: ClusterState| vrs_set.contains(vrs) ==> current_state_matches_vrs()(vrs)(s))))))) by {
                spec_entails_always_tla_forall_leads_to_always_tla_forall_within_domain(spec, desired_state_is_vrs(), current_state_matches_vrs(), vrs_set);
                assume(false); // super flaky
            }
            assume(always(tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set))) == always(tla_forall(|vrs| lift_state(|s: ClusterState| vrs_set.contains(vrs) ==> desired_state_is_vrs()(vrs)(s)))));
            assume(always(tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set))) == always(tla_forall(|vrs| lift_state(|s: ClusterState| vrs_set.contains(vrs) ==> current_state_matches_vrs()(vrs)(s)))));
        }
        leads_to_self_temp(always(lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd))));
        always_leads_to_always_combine(spec,
            lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)),
            tla_forall(lifted_conjuncted_desired_state_is_vrs(vrs_set)),
            lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)),
            tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set))
        );
        assert(spec.entails(lifted_always_vrs_set_post(vrs_set).leads_to(lifted_always_composed_post))) by {
            assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd))
                .and(tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set))).and(lifted_inv).satisfied_by(ex)
                implies #[trigger] lift_state(current_pods_match(vd)).satisfied_by(ex) by {
                conjuncted_current_state_matches_vrs_equiv_lifted(vrs_set);
                assert(conjuncted_current_state_matches_vrs(vrs_set)(ex.head())) by {
                    assert(forall |vrs| #![trigger vrs_set.contains(vrs)] lifted_conjuncted_current_state_matches_vrs(vrs_set)(vrs).satisfied_by(ex));
                    assert(forall |vrs| #[trigger] vrs_set.contains(vrs) ==> desired_state_is_vrs()(vrs)(ex.head()));
                }
                conjuncted_current_state_matches_vrs_implies_current_pods_match(vd, cluster, controller_id, vrs_set, ex.head());
            }
            entails_preserved_by_always(
                lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)).and(tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set))).and(lifted_inv),
                lift_state(current_pods_match(vd))
            );
            assume(lifted_always_vrs_set_post(vrs_set).and(always(lifted_inv)) ==
                always(lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd))
                .and(tla_forall(lifted_conjuncted_current_state_matches_vrs(vrs_set))).and(lifted_inv)));
            entails_implies_leads_to(spec, lifted_always_vrs_set_post(vrs_set).and(always(lifted_inv)), lifted_always_composed_post);
            // these helpers are hard to use
            always_double_equality(lifted_inv);
            leads_to_by_borrowing_inv(spec, lifted_always_vrs_set_post(vrs_set), lifted_always_composed_post, always(lifted_inv));
        }
        leads_to_trans(spec, lifted_always_vrs_set_pre(vrs_set), lifted_always_vrs_set_post(vrs_set), lifted_always_composed_post);
    }
    assert(spec.entails(tla_exists(lifted_always_vrs_set_pre).leads_to(lifted_always_composed_post))) by {
        leads_to_exists_intro(spec, lifted_always_vrs_set_pre, lifted_always_composed_post);
    }
    leads_to_trans_n!(spec, lifted_always_vd_pre, lifted_vd_post, tla_exists(lifted_always_vrs_set_pre), lifted_always_composed_post);
}

pub proof fn current_state_match_vd_implies_exists_vrs_set_with_desired_state_is(vd: VDeploymentView, cluster: Cluster, controller_id: int, s: ClusterState) -> (vrs_set: Set<VReplicaSetView>)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    stronger_esr(vd, controller_id)(s),
ensures
    current_state_match_vd_applied_to_vrs_set(vrs_set, vd)(s),
    conjuncted_desired_state_is_vrs(vrs_set)(s)
{
    let vrs_set = s.resources().values()
        .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
        .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
        .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd));
    // |= conjuncted_desired_state_is_vrs(vrs_set)(s)
    VReplicaSetView::marshal_preserves_integrity();
    assert(forall |vrs| #[trigger] vrs_set.contains(vrs) ==> desired_state_is_vrs()(vrs)(s));
    // from current_state_matches
    let k = choose |k: ObjectRef| {
        let etcd_obj = s.resources()[k];
        let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
        &&& #[trigger] s.resources().contains_key(k)
        &&& vd_liveness::valid_owned_obj_key(vd, s)(k)
        &&& vd_liveness::filter_new_vrs_keys(vd.spec.template, s)(k)
        &&& etcd_vrs.metadata.uid is Some
        &&& etcd_vrs.spec.replicas.unwrap_or(1) == vd.spec.replicas.unwrap_or(1)
    };
    let new_obj = s.resources()[k];
    let new_vrs = VReplicaSetView::unmarshal(s.resources()[k])->Ok_0;
    assert(vrs_set.contains(new_vrs)) by {
        assert(s.resources().values().contains(new_obj));
        assert(s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(new_obj));
    }
    assert(match_template_without_hash(vd.spec.template)(new_vrs));
    assert(new_vrs.spec.replicas.unwrap_or(1) == vd.spec.replicas.unwrap_or(1));
    if exists |old_vrs: VReplicaSetView| {
        &&& #[trigger] vrs_set.contains(old_vrs)
        &&& old_vrs != new_vrs
        &&& old_vrs.spec.replicas.unwrap_or(1) > 0
    } {
        let old_vrs = choose |old_vrs: VReplicaSetView| {
            &&& #[trigger] vrs_set.contains(old_vrs)
            &&& old_vrs != new_vrs
            &&& old_vrs.spec.replicas.unwrap_or(1) > 0
        };
        let old_k = old_vrs.object_ref();
        assert(s.resources().contains_key(old_k));
        assert(false);
    }
    return vrs_set;
}

pub proof fn conjuncted_current_state_matches_vrs_implies_current_pods_match(vd: VDeploymentView, cluster: Cluster ,controller_id: int, vrs_set: Set<VReplicaSetView>, s: ClusterState)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    conjuncted_current_state_matches_vrs(vrs_set)(s),
    current_state_match_vd_applied_to_vrs_set(vrs_set, vd)(s),
ensures
    current_pods_match(vd)(s),
{
    VReplicaSetView::marshal_preserves_integrity();
    let new_vrs = choose |vrs: VReplicaSetView| {
        &&& #[trigger] vrs_set.contains(vrs)
        &&& vrs.spec.replicas.unwrap_or(1) == vd.spec.replicas.unwrap_or(1)
        &&& match_template_without_hash(vd.spec.template)(vrs)
    };
    assert(s.resources().values().filter(valid_owned_pods(vd, s)) == vrs_liveness::matching_pods(new_vrs, s.resources())) by {
        assert forall |obj: DynamicObjectView| #[trigger] s.resources().values().contains(obj)
            implies valid_owned_pods(vd, s)(obj) == vrs_liveness::owned_selector_match_is(new_vrs, obj) by {
            if valid_owned_pods(vd, s)(obj) {
                if !vrs_liveness::owned_selector_match_is(new_vrs, obj) {
                    let havoc_vrs = choose |vrs: VReplicaSetView| {
                        &&& #[trigger] vrs_liveness::owned_selector_match_is(vrs, obj)
                        &&& valid_owned_vrs(vrs, vd)
                        &&& s.resources().contains_key(vrs.object_ref())
                        &&& VReplicaSetView::unmarshal(s.resources()[vrs.object_ref()])->Ok_0 == vrs
                    };
                    assert(vrs_set.contains(havoc_vrs)) by {
                        let havoc_obj = s.resources()[havoc_vrs.object_ref()];
                        assert(s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(havoc_obj));
                    }
                    assert(havoc_vrs.spec.replicas.unwrap_or(1) > 0) by {
                        assert(vrs_liveness::matching_pods(havoc_vrs, s.resources()).len() > 0) by {
                            assert(vrs_liveness::matching_pods(havoc_vrs, s.resources()).contains(obj));
                            // Cluster::etcd_is_finite() |= s.resources().values().is_finite()
                            injective_finite_map_implies_dom_len_is_equal_to_values_len(s.resources());
                            finite_set_to_finite_filtered_set(s.resources().values(), |obj: DynamicObjectView| vrs_liveness::owned_selector_match_is(havoc_vrs, obj));
                            lemma_set_empty_equivalency_len(vrs_liveness::matching_pods(havoc_vrs, s.resources()));
                        }
                    }
                }
            }
            if vrs_liveness::owned_selector_match_is(new_vrs, obj) {} // trivial
        }
    }
}

// similar to lemma_esr_preserves_from_s_to_s_prime
pub proof fn composed_desired_state_is_stable(
    vd: VDeploymentView, controller_id: int, cluster: Cluster, vrs_set: Set<VReplicaSetView>, s: ClusterState, s_prime: ClusterState
)
requires
    // environment invariants
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime),
    Cluster::etcd_objects_have_unique_uids()(s),
    forall |vd: VDeploymentView| #[trigger] helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s),
    vd_rely_condition(cluster, controller_id)(s),
    // lifted_vd_post
    cluster.next()(s, s_prime),
    stronger_esr(vd, controller_id)(s),
    current_state_match_vd_applied_to_vrs_set(vrs_set, vd)(s),
    conjuncted_desired_state_is_vrs(vrs_set)(s)
ensures
    stronger_esr(vd, controller_id)(s_prime),
    current_state_match_vd_applied_to_vrs_set(vrs_set, vd)(s_prime),
    conjuncted_desired_state_is_vrs(vrs_set)(s_prime)
{
    let step = choose |step| cluster.next_step(s, s_prime, step);
    assert(stronger_esr(vd, controller_id)(s_prime)) by {
        lemma_esr_preserves_from_s_to_s_prime(s, s_prime, vd, cluster, controller_id, step);
    }
    let vrs_set_prime = current_state_match_vd_implies_exists_vrs_set_with_desired_state_is(vd, cluster, controller_id, s_prime);
    assert(vrs_set == vrs_set_prime) by {
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                if msg.src != HostId::Controller(controller_id, vd.object_ref()) {
                    lemma_api_request_other_than_pending_req_msg_maintains_vrs_set_owned_by_vd(
                         s, s_prime, vd, cluster, controller_id, msg
                    );
                }
            },
            _ => {}
        }
    }
}

}