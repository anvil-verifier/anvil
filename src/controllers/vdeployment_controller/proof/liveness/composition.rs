use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::*, message::*};
use crate::reconciler::spec::io::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_lemmas::*, liveness::{spec::*, terminate, resource_match::*, proof::*, api_actions::*}, predicate::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*, util::*}
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*; // shortcut for steps
use crate::vdeployment_controller::proof::helper_invariants;
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vreplicaset_controller::trusted::liveness_theorem as vrs_liveness;
use vstd::{prelude::*, set_lib::*, map_lib::*};
use crate::vstd_ext::{set_lib::*, map_lib::*};

verus! {

// *** ESR composition helpers ***
// verus is bad at reasoning about closures
pub open spec fn desired_state_is_vrs() -> spec_fn(VReplicaSetView) -> StatePred<ClusterState> {
    |vrs: VReplicaSetView| Cluster::desired_state_is(vrs)
}

pub open spec fn current_state_matches_vrs() -> spec_fn(VReplicaSetView) -> StatePred<ClusterState> {
    |vrs: VReplicaSetView| vrs_liveness::current_state_matches(vrs)
}

pub open spec fn conjuncted_desired_state_is_vrs(vrs_set: Set<VReplicaSetView>) -> StatePred<ClusterState> {
    |s: ClusterState| (forall |vrs| #[trigger] vrs_set.contains(vrs) ==> desired_state_is_vrs()(vrs)(s))
}

pub open spec fn conjuncted_current_state_matches_vrs(vrs_set: Set<VReplicaSetView>) -> StatePred<ClusterState> {
    |s: ClusterState| (forall |vrs| #[trigger] vrs_set.contains(vrs) ==> current_state_matches_vrs()(vrs)(s))
}

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
        &&& vrs_set.finite() && vrs_set.len() > 0
    }
}

// ESR vertical composition
pub proof fn vrs_set_matches_vd_stable_state_leads_to_composed_current_state_matches_vd(spec: TempPred<ClusterState>, vd: VDeploymentView, controller_id: int, cluster: Cluster)
requires
    // environment invariants
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    // stable_vd_post
    spec.entails(always(lift_action(cluster.next()))),
    // stable spec and invariants
    spec.entails(always(lift_state(desired_state_is(vd))).leads_to(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))))),
    // ESR for vrs
    spec.entails(tla_forall(|vrs| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(current_state_matches_vrs()(vrs)))))),
    // ESR for vd, note: stability is not required
    spec.entails(always(lift_state(desired_state_is(vd))).leads_to(always(lift_state(inductive_current_state_matches(vd, controller_id))))),
    forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
        ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
ensures
    spec.entails(always(lift_state(desired_state_is(vd))).leads_to(always(lift_state(composed_current_state_matches(vd))))),
{
    vd_rely_condition_equivalent_to_lifted_vd_rely_condition(spec, cluster, controller_id);
    let lifted_inv = lift_action(cluster.next())
        .and(lifted_vd_rely_condition(cluster, controller_id))
        .and(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id));
    // get rid of lifted_vd_reconcile_request_only_interferes_with_itself_action
    assert(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id).entails(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))) by {
        assert forall |ex| #[trigger] lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id).satisfied_by(ex)
            implies lifted_vd_reconcile_request_only_interferes_with_itself(controller_id).satisfied_by(ex) by {
            assert(forall |vd: VDeploymentView| #[trigger] helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(ex.head()));
        }
    }
    entails_preserved_by_always(
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)
    );
    entails_trans(
        spec,
        always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id)),
        always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))
    );
    // spec |= [] inv
    combine_spec_entails_always_n!(
        spec,
        lifted_inv,
        lift_action(cluster.next()),
        lifted_vd_rely_condition(cluster, controller_id),
        lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)
    );
    // later we start from this spec, so we pack invariants and assumptions into it
    let stable_vd_post = lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
        .and(lift_state(inductive_current_state_matches(vd, controller_id)))
        .and(lifted_inv);
    // spec |= [] desired_state_is ~> [] (cluster_inv & inductive_current_state_matches)
    leads_to_always_combine(
        spec,
        always(lift_state(desired_state_is(vd))),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
        lift_state(inductive_current_state_matches(vd, controller_id))
    );
    // spec |= [] desired_state_is ~> [] stable_vd_post
    leads_to_always_enhance(
        spec,
        lifted_inv,
        always(lift_state(desired_state_is(vd))),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)).and(lift_state(inductive_current_state_matches(vd, controller_id))),
        stable_vd_post
    );
    let vrs_set_pre = |vrs_set| and!(
        current_state_match_vd_applied_to_vrs_set(vrs_set, vd),
        conjuncted_desired_state_is_vrs(vrs_set)
    );
    let lifted_always_vrs_set_pre = |vrs_set| always(lift_state(vrs_set_pre(vrs_set)));
    assert(always(stable_vd_post).entails(tla_exists(lifted_always_vrs_set_pre))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] always(stable_vd_post).satisfied_by(ex) implies tla_exists(|vrs_set| lift_state(vrs_set_pre(vrs_set))).satisfied_by(ex) by {
            always_to_current(ex, stable_vd_post);
            assert(cluster_invariants_since_reconciliation(cluster, vd, controller_id)(ex.head()));
            let vrs_set = current_state_match_vd_implies_exists_vrs_set_with_desired_state_is(vd, cluster, controller_id, ex.head());
            assert((|vrs_set| lift_state(vrs_set_pre(vrs_set)))(vrs_set).satisfied_by(ex));
        }
        vd_rely_condition_equivalent_to_lifted_vd_rely_condition(always(stable_vd_post), cluster, controller_id);
        let stronger_next = |s, s_prime| {
            &&& cluster.next()(s, s_prime)
            &&& inductive_current_state_matches(vd, controller_id)(s)
            &&& inductive_current_state_matches(vd, controller_id)(s_prime)
            &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
            &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime)
            &&& vd_rely_condition(cluster, controller_id)(s)
            &&& vd_reconcile_request_only_interferes_with_itself_condition(controller_id)(s)
        };
        entails_preserved_by_always(stable_vd_post, lift_state(inductive_current_state_matches(vd, controller_id)));
        always_to_always_later(always(stable_vd_post), lift_state(inductive_current_state_matches(vd, controller_id)));
        entails_preserved_by_always(stable_vd_post, lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)));
        always_to_always_later(always(stable_vd_post), lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)));
        entails_preserved_by_always(stable_vd_post, lift_action(cluster.next()));
        entails_preserved_by_always(stable_vd_post, lifted_vd_rely_condition(cluster, controller_id));
        entails_preserved_by_always(stable_vd_post, lifted_vd_reconcile_request_only_interferes_with_itself(controller_id));
        combine_spec_entails_always_n!(
            always(stable_vd_post),
            lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(inductive_current_state_matches(vd, controller_id)),
            later(lift_state(inductive_current_state_matches(vd, controller_id))),
            lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
            later(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))),
            lifted_vd_rely_condition(cluster, controller_id),
            lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)
        );
        assert forall |s, s_prime| (forall |vrs_set| #[trigger] vrs_set_pre(vrs_set)(s) && #[trigger] stronger_next(s, s_prime) ==> vrs_set_pre(vrs_set)(s_prime)) by {
            assert forall |vrs_set| #[trigger] vrs_set_pre(vrs_set)(s) && stronger_next(s, s_prime) implies vrs_set_pre(vrs_set)(s_prime) by {
                composed_desired_state_preserves_from_s_to_s_prime(vd, controller_id, cluster, vrs_set, s, s_prime);
            }
        }
        assert(tla_exists(lifted_always_vrs_set_pre) == tla_exists(|vrs_set| always(lift_state(vrs_set_pre(vrs_set)))));
        // [] stable_vd_post |= \E|vrs_set| [] vd_post_and_vrs_set_pre
        entails_exists_stable(always(stable_vd_post), stronger_next, vrs_set_pre);
    }
    // spec |= [] desired_state_is ~> \E |vrs_set| [] vd_pre_and_vrs_set_pre /\ [] stable_vd_post
    assert(spec.entails(always(lift_state(desired_state_is(vd))).leads_to(tla_exists(lifted_always_vrs_set_pre).and(always(stable_vd_post))))) by {
        entails_and_temp(
            always(stable_vd_post),
            tla_exists(lifted_always_vrs_set_pre),
            always(stable_vd_post)
        );
        entails_implies_leads_to(
            spec,
            always(stable_vd_post),
            tla_exists(lifted_always_vrs_set_pre).and(always(stable_vd_post))
        );
        leads_to_trans_n!(
            spec,
            always(lift_state(desired_state_is(vd))),
            always(stable_vd_post),
            tla_exists(lifted_always_vrs_set_pre).and(always(stable_vd_post))
        );
    }
    let lifted_vrs_set_post = |vrs_set| lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)).and(lift_state(
        conjuncted_current_state_matches_vrs(vrs_set)));
    let lifted_always_vrs_set_post = |vrs_set| always(lifted_vrs_set_post(vrs_set));
    let lifted_always_composed_post = always(lift_state(composed_current_state_matches(vd)));
    // [] vrs_set_pre == [] current_state_match_vd_applied_to_vrs_set /\ [] conjuncted_desired_state_is_vrs
    assert forall |vrs_set| #[trigger] lifted_always_vrs_set_pre(vrs_set)
        == always(lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)).and(lift_state(conjuncted_desired_state_is_vrs(vrs_set)))) by {
        and_eq(current_state_match_vd_applied_to_vrs_set(vrs_set, vd), conjuncted_desired_state_is_vrs(vrs_set));
        temp_pred_equality(
            lifted_always_vrs_set_pre(vrs_set),
            always(lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)).and(lift_state(conjuncted_desired_state_is_vrs(vrs_set))))
        );
    }
    // [] vrs_set_post == [] current_state_match_vd_applied_to_vrs_set /\ [] conjuncted_current_state_matches_vrs
    assert forall |vrs_set| #[trigger] lifted_always_vrs_set_post(vrs_set)
        == always(lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)).and(lift_state(conjuncted_current_state_matches_vrs(vrs_set)))) by {
        always_and_equality(
            lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)),
            lift_state(conjuncted_current_state_matches_vrs(vrs_set))
        );
    }
    // spec |= \E |vrs_set| [] vd_pre_and_vrs_set_pre ~> \E |vrs_set| [] vd_post_and_vrs_set_post
    assert(spec.entails(tla_exists(lifted_always_vrs_set_pre).leads_to(tla_exists(lifted_always_vrs_set_post)))) by {
        let pre = |vrs_set: Set<VReplicaSetView>| vrs_set.finite() && vrs_set.len() > 0;
        assert forall |vrs_set: Set<VReplicaSetView>| pre(vrs_set)
            implies #[trigger] spec.entails(lifted_always_vrs_set_pre(vrs_set).leads_to(tla_exists(lifted_always_vrs_set_post))) by {
            always_and_equality(
                lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)),
                lift_state(conjuncted_desired_state_is_vrs(vrs_set))
            );
            assert(spec.entails(always(lift_state(conjuncted_desired_state_is_vrs(vrs_set))).leads_to(always(lift_state(conjuncted_current_state_matches_vrs(vrs_set)))))) by {
                assert forall |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs) implies
                    spec.entails(always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(current_state_matches_vrs()(vrs))))) by {
                    use_tla_forall(spec, |vrs| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(current_state_matches_vrs()(vrs)))), vrs);
                }
                spec_entails_always_tla_forall_leads_to_always_tla_forall_within_domain(
                    spec, desired_state_is_vrs(), current_state_matches_vrs(), vrs_set,
                    conjuncted_desired_state_is_vrs(vrs_set), conjuncted_current_state_matches_vrs(vrs_set)
                );
            }
            leads_to_self_temp(always(lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd))));
            always_leads_to_always_combine(spec,
                lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)),
                lift_state(conjuncted_desired_state_is_vrs(vrs_set)),
                lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)),
                lift_state(conjuncted_current_state_matches_vrs(vrs_set))
            );
            entails_exists_intro(lifted_always_vrs_set_post, vrs_set);
            entails_implies_leads_to(
                spec,
                lifted_always_vrs_set_post(vrs_set),
                tla_exists(lifted_always_vrs_set_post)
            );
            leads_to_trans(
                spec,
                lifted_always_vrs_set_pre(vrs_set),
                lifted_always_vrs_set_post(vrs_set),
                tla_exists(lifted_always_vrs_set_post)
            );
        }
        assert forall |vrs_set: Set<VReplicaSetView>| lifted_always_vrs_set_pre(vrs_set).entails(lift_state(|s: ClusterState| #[trigger] pre(vrs_set))) by {
            always_entails_current(lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)).and(lift_state(conjuncted_desired_state_is_vrs(vrs_set))));
            entails_trans_n!(
                lifted_always_vrs_set_pre(vrs_set),
                lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)).and(lift_state(conjuncted_desired_state_is_vrs(vrs_set))),
                lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)),
                lift_state(|s: ClusterState| #[trigger] pre(vrs_set))
            );
        }
        leads_to_exists_intro_with_pre(spec, lifted_always_vrs_set_pre, tla_exists(lifted_always_vrs_set_post), pre);
    }
    // spec |= (\E |vrs_set| [] vrs_set_pre) /\ [] stable_vd_post ~> (\E |vrs_set| [] vd_post_and_vrs_set_post) /\ [] stable_vd_post
    assert(spec.entails(tla_exists(lifted_always_vrs_set_pre).and(always(stable_vd_post))
        .leads_to(tla_exists(lifted_always_vrs_set_post).and(always(stable_vd_post)))) ) by {
        let lifted_vrs_set_pre = |vrs_set| lift_state(vrs_set_pre(vrs_set));
        assert forall |vrs_set| #[trigger] lifted_always_vrs_set_pre(vrs_set)
            == always(lifted_vrs_set_pre(vrs_set)) by {
            temp_pred_equality(
                lifted_always_vrs_set_pre(vrs_set),
                always(lifted_vrs_set_pre(vrs_set))
            );
        }
        tla_exists_p_tla_exists_q_equality(
            lifted_always_vrs_set_pre,
            |vrs_set| always(lifted_vrs_set_pre(vrs_set))
        );
        temp_pred_equality(
            tla_exists(lifted_always_vrs_set_post),
            tla_exists(|vrs_set| always(lifted_vrs_set_post(vrs_set)))
        );
        leads_to_with_always(
            spec,
            tla_exists(lifted_always_vrs_set_pre),
            tla_exists(lifted_always_vrs_set_post),
            stable_vd_post
        );
    }
    // [] stable_vd_post |= \E |vrs_set| [] vd_post_and_vrs_set_post ~> [] composed_post
    assert forall |vrs_set: Set<VReplicaSetView>| always(stable_vd_post).entails(#[trigger] lifted_always_vrs_set_post(vrs_set).leads_to(lifted_always_composed_post)) by {
        let stable_inv = lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id));
        assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd))
            .and(lift_state(conjuncted_current_state_matches_vrs(vrs_set))).and(stable_inv).satisfied_by(ex)
            implies #[trigger] lift_state(composed_current_state_matches(vd)).satisfied_by(ex) by {
            conjuncted_current_state_matches_vrs_implies_composed_current_state_matches(vd, cluster, controller_id, vrs_set, ex.head());
        }
        entails_preserved_by_always(
            lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)).and(lift_state(conjuncted_current_state_matches_vrs(vrs_set))).and(stable_inv),
            lift_state(composed_current_state_matches(vd))
        );
        assert(lifted_always_vrs_set_post(vrs_set).and(always(stable_inv)) == always(lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd))
            .and(lift_state(conjuncted_current_state_matches_vrs(vrs_set))).and(stable_inv))) by {
            always_and_equality(
                lift_state(current_state_match_vd_applied_to_vrs_set(vrs_set, vd)).and(lift_state(conjuncted_current_state_matches_vrs(vrs_set))),
                stable_inv
            );
        }
        entails_implies_leads_to(always(stable_vd_post), lifted_always_vrs_set_post(vrs_set).and(always(stable_inv)), lifted_always_composed_post);
        // these helpers are hard to use
        always_double_equality(stable_inv);
        entails_preserved_by_always(stable_vd_post, stable_inv);
        leads_to_by_borrowing_inv(always(stable_vd_post), lifted_always_vrs_set_post(vrs_set), lifted_always_composed_post, always(stable_inv));
    }
    leads_to_exists_intro(always(stable_vd_post), lifted_always_vrs_set_post, lifted_always_composed_post);
    temp_pred_equality(
        true_pred().and(always(stable_vd_post)),
        always(stable_vd_post)
    );
    // true |= [] stable_vd_post /\ \E |vrs_set| [] vd_post_and_vrs_set_post ~> [] composed_post
    unpack_conditions_from_spec(true_pred(), always(stable_vd_post), tla_exists(lifted_always_vrs_set_post), lifted_always_composed_post);
    temp_pred_equality(
        always(stable_vd_post).and(tla_exists(lifted_always_vrs_set_post)),
        tla_exists(lifted_always_vrs_set_post).and(always(stable_vd_post))
    );
    // spec |= (([] stable_vd_post /\ \E |vrs_set| [] vd_post_and_vrs_set_post) ~> [] composed_post) /\ spec
    entails_and_different_temp(
        true_pred(),
        spec,
        always(stable_vd_post).and(tla_exists(lifted_always_vrs_set_post)).leads_to(lifted_always_composed_post),
        spec
    );
    temp_pred_equality(
        true_pred().and(spec),
        spec
    );
    // spec |= ([] stable_vd_post /\ \E |vrs_set| [] vd_post_and_vrs_set_post) ~> [] composed_post
    entails_trans(
        spec,
        always(stable_vd_post).and(tla_exists(lifted_always_vrs_set_post)).leads_to(lifted_always_composed_post).and(spec),
        always(stable_vd_post).and(tla_exists(lifted_always_vrs_set_post)).leads_to(lifted_always_composed_post)
    );
    assert(spec.entails(always(lift_state(desired_state_is(vd))).leads_to(lifted_always_composed_post))) by {
        leads_to_trans_n!(
            spec,
            always(lift_state(desired_state_is(vd))),
            tla_exists(lifted_always_vrs_set_pre).and(always(stable_vd_post)),
            tla_exists(lifted_always_vrs_set_post).and(always(stable_vd_post)),
            lifted_always_composed_post
        );
    }
}

pub proof fn current_state_match_vd_implies_exists_vrs_set_with_desired_state_is(vd: VDeploymentView, cluster: Cluster, controller_id: int, s: ClusterState) -> (vrs_set: Set<VReplicaSetView>)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    inductive_current_state_matches(vd, controller_id)(s),
ensures
    current_state_match_vd_applied_to_vrs_set(vrs_set, vd)(s),
    conjuncted_desired_state_is_vrs(vrs_set)(s),
    vrs_set.finite(),
    vrs_set.len() > 0,
{
    let vrs_set = s.resources().values()
        .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
        .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
        .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd));
    assert(vrs_set.finite()) by {
        lemma_values_finite(s.resources());
        finite_set_to_finite_filtered_set(s.resources().values(), |obj: DynamicObjectView| obj.kind == VReplicaSetView::kind());
        s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .lemma_map_finite(|obj: DynamicObjectView| VReplicaSetView::unmarshal(obj)->Ok_0);
        finite_set_to_finite_filtered_set(
            s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
                .map(|obj: DynamicObjectView| VReplicaSetView::unmarshal(obj)->Ok_0),
            |vrs: VReplicaSetView| valid_owned_vrs(vrs, vd)
        );
    }
    // |= conjuncted_desired_state_is_vrs(vrs_set)(s)
    VReplicaSetView::marshal_preserves_integrity();
    assert(forall |vrs| #[trigger] vrs_set.contains(vrs) ==> Cluster::desired_state_is(vrs)(s));
    // from current_state_matches
    let k = choose |k: ObjectRef| {
        let etcd_obj = s.resources()[k];
        let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
        &&& #[trigger] s.resources().contains_key(k)
        &&& valid_owned_obj_key(vd, s)(k)
        &&& filter_new_vrs_keys(vd.spec.template, s)(k)
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

pub proof fn conjuncted_current_state_matches_vrs_implies_composed_current_state_matches(vd: VDeploymentView, cluster: Cluster ,controller_id: int, vrs_set: Set<VReplicaSetView>, s: ClusterState)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    conjuncted_current_state_matches_vrs(vrs_set)(s),
    current_state_match_vd_applied_to_vrs_set(vrs_set, vd)(s),
ensures
    composed_current_state_matches(vd)(s),
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

// similar to lemma_inductive_current_state_matches_preserves_from_s_to_s_prime
pub proof fn composed_desired_state_preserves_from_s_to_s_prime(
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
    vd_reconcile_request_only_interferes_with_itself_condition(controller_id)(s),
    vd_rely_condition(cluster, controller_id)(s),
    // stable_vd_post
    cluster.next()(s, s_prime),
    inductive_current_state_matches(vd, controller_id)(s),
    inductive_current_state_matches(vd, controller_id)(s_prime),
    current_state_match_vd_applied_to_vrs_set(vrs_set, vd)(s),
    conjuncted_desired_state_is_vrs(vrs_set)(s)
ensures
    current_state_match_vd_applied_to_vrs_set(vrs_set, vd)(s_prime),
    conjuncted_desired_state_is_vrs(vrs_set)(s_prime)
{
    let step = choose |step| cluster.next_step(s, s_prime, step);
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

pub open spec fn vrs_is_the_only_non_zero_vrs_with_updated_spec(vd: VDeploymentView, vrs_key: ObjectRef, s: ClusterState) -> bool {
    s.resources().dom().filter(|k: ObjectRef| {
        let obj = s.resources()[k];
        let vrs = VReplicaSetView::unmarshal(obj)->Ok_0;
        &&& valid_owned_obj_key(vd, s)(k)
        &&& vrs.spec.replicas.unwrap_or(1) > 0
        &&& match_template_without_hash(vd.spec.template)(vrs)
    }) == set![vrs_key]
}

// replicas > 0
pub open spec fn desired_state_is_with_replicas(replicas: int, vrs: VReplicaSetView, vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let vrs_with_replicas = vrs.with_spec(vrs.spec.with_replicas(replicas));
        // 1. desired_state_is
        &&& Cluster::desired_state_is(vrs_with_replicas)(s)
        // 2. vd controller will not select other VRS to scale up
        &&& vrs_is_the_only_non_zero_vrs_with_updated_spec(vrs.object_ref())
    }
}

pub open spec fn current_state_matches_with_replicas(replicas: int, vrs: VReplicaSetView, vd: VDeploymentView) -> StatePred<ClusterState> {
    let etcd_vrs = VReplicaSetView::unmarshal(s.resources()[vrs.object_ref()])->Ok_0
    // 1. current_state_matches
    &&& current_state_matches_vrs(vrs.with_spec(vrs.spec.with_replicas(replicas)))
    // 2. vd controller will not select other VRS to scale up
    &&& vrs_is_the_only_non_zero_vrs_with_updated_spec(vrs.object_ref())
    // 3. number of running pods is written to status
    &&& etcd_vrs.status is Some
    &&& etcd_vrs.status->0.replicas == replicas
}

pub proof fn desired_state_is_with_replicas_of_n_leads_to_desired_state_is_with_replicas_of_zero_by_rolling_update(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, vd: VDeploymentView
)
ensures
    true,
{
    let p = |replicas_left: n| desired_state_is_with_replicas(vd.spec.replicas.unwrap_or(1) - replicas, vrs, vd);
    let q = |replicas_left: n| current_state_matches_with_replicas(vd.spec.replicas.unwrap_or(1) - replicas, vrs, vd);
    // VRS ESR, current proofs can be reused
    assume(forall |n| #![trigger p(n)] spec.entails(always(p(n)).leads_to(always(q(n)))));
    // VD guarantee: never scale down updated VRS (new proof)
    assume(forall |n| #![trigger p(n)] spec.entails(always(p(n).implies(always(tla_exists(|m: nat| lift_state(|s| m <= n).and(p(m))))))));
    // VD ESR after rolling update (new proof, some can be reused)
    assume(forall |n: nat| #![trigger p(n)] n > 0 ==> spec.entails(always(q(n)).leads_to(not(p(n)))));
    leads_to_by_monotonicity3(spec, p, q);
}

}