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

// *** Rolling update ESR composition helpers ***
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

// Compute the absolute difference between desired replicas and new VRS replicas
// This is the ranking function for leads_to_by_monotonicity3
pub open spec fn replicas_diff(vd: VDeploymentView, new_vrs: VReplicaSetView) -> nat {
    let desired = vd.spec.replicas.unwrap_or(1);
    let current = new_vrs.spec.replicas.unwrap_or(1);
    if desired >= current {
        (desired - current) as nat
    } else {
        (current - desired) as nat
    }
}

// p(n) for leads_to_by_monotonicity3 (parameterized by fixed vrs_set):
// All VRS in vrs_set have desired_state_is, and there exists a new VRS in vrs_set
// whose template matches and whose replicas diff from vd.spec.replicas is n.
pub open spec fn conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set: Set<VReplicaSetView>, vd: VDeploymentView, n: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& (forall |vrs| #[trigger] vrs_set.contains(vrs) ==> desired_state_is_vrs()(vrs)(s))
        &&& exists |new_vrs: VReplicaSetView| {
            &&& #[trigger] vrs_set.contains(new_vrs)
            &&& match_template_without_hash(vd.spec.template)(new_vrs)
            &&& replicas_diff(vd, new_vrs) == n
        }
    }
}

// q(n) for leads_to_by_monotonicity3 (parameterized by fixed vrs_set):
// All VRS in vrs_set have current_state_matches, and there exists a new VRS in vrs_set
// whose template matches and whose replicas diff from vd.spec.replicas is n.
pub open spec fn conjuncted_current_state_matches_vrs_with_replica_diff(vrs_set: Set<VReplicaSetView>, vd: VDeploymentView, n: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& (forall |vrs| #[trigger] vrs_set.contains(vrs) ==> current_state_matches_vrs()(vrs)(s))
        &&& exists |new_vrs: VReplicaSetView| {
            &&& #[trigger] vrs_set.contains(new_vrs)
            &&& match_template_without_hash(vd.spec.template)(new_vrs)
            &&& replicas_diff(vd, new_vrs) == n
        }
    }
}

// Strip resource_version AND status for vrs_set identity stability.
// When VD controller changes replicas via GetThenUpdate, or VRS controller changes status,
// the mapped set remains the same.
// spec.replicas is passed as argument in higher level predicates
pub open spec fn map_vrs_for_identity(vrs: VReplicaSetView) -> VReplicaSetView {
    VReplicaSetView {
        metadata: vrs.metadata.without_resource_version(),
        status: None,
        ..vrs
    }
}

// vrs_set identity check modulo rv/status/replicas, plus replicas constraints:
// - new VRS has replicas such that diff from vd.spec.replicas is n
// - all non-new VRS have replicas == Some(0)
pub open spec fn current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set: Set<VReplicaSetView>, vd: VDeploymentView, n: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& vrs_set.map(|vrs: VReplicaSetView| map_vrs_for_identity(vrs)) == s.resources().values()
            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
            .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd))
            .map(|vrs: VReplicaSetView| map_vrs_for_identity(vrs))
        &&& exists |new_vrs: VReplicaSetView| {
            &&& #[trigger] vrs_set.contains(new_vrs)
            &&& match_template_without_hash(vd.spec.template)(new_vrs)
            &&& replicas_diff(vd, new_vrs) == n
            // all old vrs have replicas == Some(0)
            &&& !exists |old_vrs: VReplicaSetView| {
                &&& #[trigger] vrs_set.contains(old_vrs)
                &&& old_vrs != new_vrs
                &&& old_vrs.spec.replicas.unwrap_or(1) > 0
            }
        }
        &&& vrs_set.finite() && vrs_set.len() > 0
    }
}

// *** Obligation proofs for leads_to_by_monotonicity3 (per fixed vrs_set) ***

// Obligation 1: ESR for each ranking level
// forall n. spec |= [] p(n) ~> [] q(n)
pub proof fn esr_for_each_ranking(
    spec: TempPred<ClusterState>,
    vrs_set: Set<VReplicaSetView>,
    vd: VDeploymentView,
    n: nat,
)
    requires
        vrs_set.finite(),
        vrs_set.len() > 0,
        spec.entails(tla_forall(|vrs| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(current_state_matches_vrs()(vrs)))))),
    ensures
        spec.entails(
            always(lift_state(conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, n)))
            .leads_to(always(lift_state(conjuncted_current_state_matches_vrs_with_replica_diff(vrs_set, vd, n))))
        ),
{
    // Instantiate VRS ESR for each vrs in the set
    assert forall |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs) implies
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(current_state_matches_vrs()(vrs))))) by {
        use_tla_forall(spec, |vrs| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(current_state_matches_vrs()(vrs)))), vrs);
    }
    // Compose individual VRS ESRs into the conjuncted form
    // [] (forall vrs in set, desired_state_is(vrs)) ~> [] (forall vrs in set, current_state_matches(vrs))
    spec_entails_always_tla_forall_leads_to_always_tla_forall_within_domain(
        spec, desired_state_is_vrs(), current_state_matches_vrs(), vrs_set,
        conjuncted_desired_state_is_vrs(vrs_set), conjuncted_current_state_matches_vrs(vrs_set)
    );
    if exists |new_vrs: VReplicaSetView| #[trigger] vrs_set.contains(new_vrs) && match_template_without_hash(vd.spec.template)(new_vrs) && replicas_diff(vd, new_vrs) == n {
        temp_pred_equality(
            lift_state(conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, n)),
            lift_state(conjuncted_desired_state_is_vrs(vrs_set))
        );
        temp_pred_equality(
            lift_state(conjuncted_current_state_matches_vrs_with_replica_diff(vrs_set, vd, n)),
            lift_state(conjuncted_current_state_matches_vrs(vrs_set))
        );
    } else {
        temp_pred_equality(
            lift_state(conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, n)),
            false_pred()
        );
        false_is_stable::<ClusterState>();
        stable_to_always::<ClusterState>(false_pred());
        false_leads_to(spec, always(lift_state(conjuncted_current_state_matches_vrs_with_replica_diff(vrs_set, vd, n))));
    }
}

// Obligation 2: Monotonicity (ranking never increases)
// forall n. spec |= [] (p(n) => [] (exists m <= n. p(m)))
#[verifier(external_body)]
pub proof fn ranking_never_increases(
    spec: TempPred<ClusterState>,
    vrs_set: Set<VReplicaSetView>,
    vd: VDeploymentView,
    controller_id: int,
    cluster: Cluster,
    n: nat,
)
    requires
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures
        spec.entails(
            always(lift_state(conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, n))
                .and(lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)))
            .implies(always(tla_exists(|m: nat| lift_state(|s| m <= n)
                .and(lift_state(conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, m))
                .and(lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, m))))
            ))))
        ),
{}

// Obligation 3: Ranking decrease
// forall n > 0. spec |= [] q(n) ~> !p(n)
#[verifier(external_body)]
pub proof fn ranking_decreases_after_vrs_esr(
    spec: TempPred<ClusterState>,
    vrs_set: Set<VReplicaSetView>,
    vd: VDeploymentView,
    controller_id: int,
    cluster: Cluster,
    n: nat,
)
    requires
        n > 0,
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
        spec.entails(always(lift_state(desired_state_is(vd))).leads_to(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures
        spec.entails(
            always(
                lift_state(conjuncted_current_state_matches_vrs_with_replica_diff(vrs_set, vd, n))
                    .and(lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)))
            ).leads_to(not(
                lift_state(conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, n))
                    .and(lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)))
            ))
        ),
{}

// *** Helper lemmas ***

// From inductive_current_state_matches, extract (vrs_set, n) witness
pub proof fn current_state_match_vd_implies_exists_vrs_set_with_replica_diff(
    vd: VDeploymentView,
    cluster: Cluster,
    controller_id: int,
    s: ClusterState
) -> (res: (Set<VReplicaSetView>, nat))
    requires
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
        inductive_current_state_matches(vd, controller_id)(s),
    ensures
        current_state_match_vd_applied_to_vrs_set_with_replicas(res.0, vd, res.1)(s),
        conjuncted_desired_state_is_vrs_with_replica_diff(res.0, vd, res.1)(s),
        res.0.finite(),
        res.0.len() > 0,
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
        &&& replicas_match_status(etcd_vrs, vd.spec.replicas.unwrap_or(1))
        &&& !exists |old_k: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(old_k)
            &&& valid_owned_obj_key(vd, s)(old_k)
            &&& filter_old_vrs_keys(Some(etcd_vrs.metadata.uid->0), s)(old_k)
        }
    };
    let new_obj = s.resources()[k];
    let new_vrs = VReplicaSetView::unmarshal(s.resources()[k])->Ok_0;
    assert(vrs_set.contains(new_vrs)) by {
        assert(s.resources().values().contains(new_obj));
        assert(s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(new_obj));
    }
    assert(match_template_without_hash(vd.spec.template)(new_vrs));
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
        assert(s.resources().contains_key(old_k)); // trigger
        assert(false);
    }
    return (vrs_set, replicas_diff(vd, new_vrs));
}

// q(0) with vrs_set identity implies composed_current_state_matches
pub proof fn conjuncted_current_state_matches_vrs_with_replica_diff_0_implies_composed(
    vd: VDeploymentView,
    cluster: Cluster,
    controller_id: int,
    vrs_set: Set<VReplicaSetView>,
    s: ClusterState,
)
    requires
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
        conjuncted_current_state_matches_vrs_with_replica_diff(vrs_set, vd, 0)(s),
        current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, 0)(s),
    ensures
        composed_current_state_matches(vd)(s),
{
    VReplicaSetView::marshal_preserves_integrity();
    let new_vrs = choose |vrs: VReplicaSetView| {
        &&& #[trigger] vrs_set.contains(vrs)
        &&& match_template_without_hash(vd.spec.template)(vrs)
        &&& replicas_diff(vd, vrs) == 0
    };
    assert(s.resources().values().filter(valid_owned_pods(vd, s)) == vrs_liveness::matching_pods(new_vrs, s.resources())) by {
        assert forall |obj: DynamicObjectView| #[trigger] s.resources().values().contains(obj)
            implies valid_owned_pods(vd, s)(obj) == vrs_liveness::owned_selector_match_is(new_vrs, obj) by {
            if valid_owned_pods(vd, s)(obj) && !vrs_liveness::owned_selector_match_is(new_vrs, obj) {
                let havoc_vrs = choose |vrs: VReplicaSetView| {
                    &&& #[trigger] vrs_liveness::owned_selector_match_is(vrs, obj)
                    &&& valid_owned_vrs(vrs, vd)
                    &&& s.resources().contains_key(vrs.object_ref())
                    &&& VReplicaSetView::unmarshal(s.resources()[vrs.object_ref()])->Ok_0 == vrs
                };
                assert(vrs_set.map(|vrs: VReplicaSetView| map_vrs_for_identity(vrs)).contains(map_vrs_for_identity(havoc_vrs))) by {
                    let etcd_obj = s.resources()[havoc_vrs.object_ref()];
                    assert(s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(etcd_obj));
                    let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
                    assert(s.resources().values()
                        .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
                        .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
                        .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd))
                        .contains(etcd_vrs));
                    assert(map_vrs_for_identity(havoc_vrs) == map_vrs_for_identity(etcd_vrs));
                }
                assert(exists |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs) 
                    && map_vrs_for_identity(vrs) == map_vrs_for_identity(havoc_vrs) && vrs != new_vrs);
                let havoc_vrs_in_set = choose |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs)
                    && map_vrs_for_identity(vrs) == map_vrs_for_identity(havoc_vrs) && vrs != new_vrs;
                assert(havoc_vrs_in_set.spec.replicas.unwrap_or(1) > 0) by {
                    assert(vrs_liveness::matching_pods(havoc_vrs_in_set, s.resources()).len() > 0) by {
                        assert(vrs_liveness::matching_pods(havoc_vrs_in_set, s.resources()).contains(obj));
                        // Cluster::etcd_is_finite() |= s.resources().values().is_finite()
                        injective_finite_map_implies_dom_len_is_equal_to_values_len(s.resources());
                        finite_set_to_finite_filtered_set(s.resources().values(), |obj: DynamicObjectView| vrs_liveness::owned_selector_match_is(havoc_vrs_in_set, obj));
                        lemma_set_empty_equivalency_len(vrs_liveness::matching_pods(havoc_vrs_in_set, s.resources()));
                    }
                }
                assert(false);
            }
            if vrs_liveness::owned_selector_match_is(new_vrs, obj) && !valid_owned_pods(vd, s)(obj) {
                assert(vrs_set.map(|vrs: VReplicaSetView| map_vrs_for_identity(vrs)).contains(map_vrs_for_identity(new_vrs)));
                let mapped_vrs_set_in_etcd = s.resources().values()
                    .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
                    .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
                    .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd))
                    .map(|vrs: VReplicaSetView| map_vrs_for_identity(vrs));
                assert(exists |vrs: VReplicaSetView| #[trigger] mapped_vrs_set_in_etcd.contains(vrs) && vrs == map_vrs_for_identity(new_vrs));
                let mapped_new_vrs_in_etcd = choose |vrs: VReplicaSetView| #[trigger] mapped_vrs_set_in_etcd.contains(vrs) && vrs == map_vrs_for_identity(new_vrs);
                let vrs_set_in_etcd = s.resources().values()
                    .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
                    .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
                    .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd));
                assert(exists |vrs: VReplicaSetView| #[trigger] vrs_set_in_etcd.contains(vrs) && map_vrs_for_identity(vrs) == mapped_new_vrs_in_etcd);
                let new_vrs_in_etcd = choose |vrs: VReplicaSetView| #[trigger] vrs_set_in_etcd.contains(vrs) && map_vrs_for_identity(vrs) == mapped_new_vrs_in_etcd;
                assert(map_vrs_for_identity(new_vrs_in_etcd) == map_vrs_for_identity(new_vrs));
                assert({
                    &&& #[trigger] vrs_liveness::owned_selector_match_is(new_vrs_in_etcd, obj)
                    &&& valid_owned_vrs(new_vrs_in_etcd, vd)
                    &&& s.resources().contains_key(new_vrs_in_etcd.object_ref())
                    &&& VReplicaSetView::unmarshal(s.resources()[new_vrs_in_etcd.object_ref()])->Ok_0 == new_vrs_in_etcd
                });
                assert(false);
            }
        }
    }
}

// Stability of vrs_set identity (modulo rv/status/replicas) and conjuncted p(n)
#[verifier(external_body)]
pub proof fn rolling_update_desired_state_preserves_from_s_to_s_prime(
    vd: VDeploymentView,
    controller_id: int,
    cluster: Cluster,
    vrs_set: Set<VReplicaSetView>,
    n: nat,
    s: ClusterState,
    s_prime: ClusterState,
)
    requires
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
        cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime),
        Cluster::etcd_objects_have_unique_uids()(s),
        vd_reconcile_request_only_interferes_with_itself_condition(controller_id)(s),
        vd_rely_condition(cluster, controller_id)(s),
        cluster.next()(s, s_prime),
        inductive_current_state_matches(vd, controller_id)(s),
        inductive_current_state_matches(vd, controller_id)(s_prime),
        current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)(s),
        conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, n)(s),
    ensures
        current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)(s_prime),
        conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, n)(s_prime),
{}

// *** Top-level rolling update ESR composition theorem ***
pub proof fn rolling_update_leads_to_composed_current_state_matches_vd(
    spec: TempPred<ClusterState>,
    vd: VDeploymentView,
    controller_id: int,
    cluster: Cluster,
)
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
        // ESR for vd (with rolling update behavior)
        spec.entails(always(lift_state(desired_state_is(vd))).leads_to(always(lift_state(inductive_current_state_matches(vd, controller_id))))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures
        spec.entails(always(lift_state(desired_state_is(vd))).leads_to(always(lift_state(composed_current_state_matches(vd))))),
{
    // -- Step 1: Pack invariants into stable_vd_post (same as original composition.rs) --
    vd_rely_condition_equivalent_to_lifted_vd_rely_condition(spec, cluster, controller_id);
    let lifted_inv = lift_action(cluster.next())
        .and(lifted_vd_rely_condition(cluster, controller_id))
        .and(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id));
    assert(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id).entails(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))) by {
        assert forall |ex| #[trigger] lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id).satisfied_by(ex)
            implies lifted_vd_reconcile_request_only_interferes_with_itself(controller_id).satisfied_by(ex) by {
            assert(forall |vd: VDeploymentView| #[trigger] helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(ex.head()));
        }
    };
    entails_preserved_by_always(
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)
    );
    entails_trans(
        spec,
        always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id)),
        always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))
    );
    combine_spec_entails_always_n!(
        spec,
        lifted_inv,
        lift_action(cluster.next()),
        lifted_vd_rely_condition(cluster, controller_id),
        lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)
    );
    let stable_vd_post = lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
        .and(lift_state(inductive_current_state_matches(vd, controller_id)))
        .and(lifted_inv);

    // -- Step 2: spec |= [] desired_state_is ~> [] stable_vd_post --
    leads_to_always_combine(
        spec,
        always(lift_state(desired_state_is(vd))),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
        lift_state(inductive_current_state_matches(vd, controller_id))
    );
    leads_to_always_enhance(
        spec,
        lifted_inv,
        always(lift_state(desired_state_is(vd))),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)).and(lift_state(inductive_current_state_matches(vd, controller_id))),
        stable_vd_post
    );

    // -- Step 3: [] stable_vd_post |= \E (vrs_set, n) [] vrs_set_pre(vrs_set, n) --
    // Define vrs_set_pre combining identity and conjuncted_desired_state_is with replicas
    let vrs_set_pre = |vrs_set_with_diff: (Set<VReplicaSetView>, nat)| and!(
        current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set_with_diff.0, vd, vrs_set_with_diff.1),
        conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set_with_diff.0, vd, vrs_set_with_diff.1)
    );
    let lifted_always_vrs_set_pre = |vrs_set_with_diff: (Set<VReplicaSetView>, nat)| always(lift_state(vrs_set_pre(vrs_set_with_diff)));

    // Show [] stable_vd_post |= \E (vrs_set, n) [] vrs_set_pre via entails_exists_stable
    assert(always(stable_vd_post).entails(tla_exists(lifted_always_vrs_set_pre))) by {
        // First show that [] stable_vd_post |= \E (vrs_set, n) vrs_set_pre (existence at current state)
        assert forall |ex: Execution<ClusterState>| #[trigger] always(stable_vd_post).satisfied_by(ex)
            implies tla_exists(|vrs_set_with_diff| lift_state(vrs_set_pre(vrs_set_with_diff))).satisfied_by(ex) by {
            always_to_current(ex, stable_vd_post);
            assert(cluster_invariants_since_reconciliation(cluster, vd, controller_id)(ex.head()));
            let (vrs_set, n) = current_state_match_vd_implies_exists_vrs_set_with_replica_diff(vd, cluster, controller_id, ex.head());
            assert((|vrs_set_with_diff: (Set<VReplicaSetView>, nat)| lift_state(vrs_set_pre(vrs_set_with_diff)))((vrs_set, n)).satisfied_by(ex));
        }
        // Then show stability: vrs_set_pre is preserved by transitions under stable_vd_post
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
        assert forall |s, s_prime| (forall |vrs_set_with_diff: (Set<VReplicaSetView>, nat)|
            #[trigger] vrs_set_pre(vrs_set_with_diff)(s) && #[trigger] stronger_next(s, s_prime)
                ==> vrs_set_pre(vrs_set_with_diff)(s_prime)) by {
            assert forall |vrs_set_with_diff: (Set<VReplicaSetView>, nat)|
                #[trigger] vrs_set_pre(vrs_set_with_diff)(s) && stronger_next(s, s_prime)
                    implies vrs_set_pre(vrs_set_with_diff)(s_prime) by {
                rolling_update_desired_state_preserves_from_s_to_s_prime(
                    vd, controller_id, cluster, vrs_set_with_diff.0, vrs_set_with_diff.1, s, s_prime
                );
            }
        }
        assert(tla_exists(lifted_always_vrs_set_pre) == tla_exists(|vrs_set_with_diff| always(lift_state(vrs_set_pre(vrs_set_with_diff)))));
        entails_exists_stable(always(stable_vd_post), stronger_next, vrs_set_pre);
    }

    // -- Step 4: For each vrs_set, apply leads_to_by_monotonicity3 --
    // p(n) ~> [] p(0), then [] p(0) ~> [] q(0), then [] q(0) ~> composed
    // Use leads_to_exists_intro to lift over the existential

    // For each fixed (vrs_set, n_init), show:
    //   [] vrs_set_pre(vrs_set, n_init) /\ [] stable_vd_post ~> [] composed_post
    let lifted_always_composed_post = always(lift_state(composed_current_state_matches(vd)));

    // Apply monotonicity3 for each fixed vrs_set:
    // For fixed vrs_set, let p_vrs = |n| lift_state(conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, n))
    // and q_vrs = |n| lift_state(conjuncted_current_state_matches_vrs_with_replica_diff(vrs_set, vd, n))
    // leads_to_by_monotonicity3 gives: p_vrs(n) ~> [] p_vrs(0)
    // Then: [] p_vrs(0) ~> [] q_vrs(0) (by esr_for_each_ranking)
    // Then: [] q_vrs(0) with vrs_set identity ~> [] composed (by final step lemma)

    let pre = |vrs_set_with_diff: (Set<VReplicaSetView>, nat)| vrs_set_with_diff.0.finite() && vrs_set_with_diff.0.len() > 0;
    assert forall |vrs_set_with_diff: (Set<VReplicaSetView>, nat)| pre(vrs_set_with_diff)
        implies #[trigger] spec.entails(
            lifted_always_vrs_set_pre(vrs_set_with_diff).and(always(stable_vd_post)).leads_to(lifted_always_composed_post)
        ) by {
        let vrs_set = vrs_set_with_diff.0;
        let n_init = vrs_set_with_diff.1;
        // p_vrs and q_vrs include both the conjuncted predicate AND the vrs_set identity
        let identity = |n: nat| lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n));
        let p_vrs = |n: nat| lift_state(conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, n))
            .and(identity(n));
        let q_vrs = |n: nat| lift_state(conjuncted_current_state_matches_vrs_with_replica_diff(vrs_set, vd, n))
            .and(identity(n));

        // Obligation 1: [] p_vrs(n) ~> [] q_vrs(n)
        // Use always_leads_to_always_combine to combine ESR with identity self-leads-to
        assert forall |n: nat| #![trigger p_vrs(n)]
            spec.entails(always(p_vrs(n)).leads_to(always(q_vrs(n)))) by {
            // [] desired_state_is_vrs_with_replicas ~> [] current_state_matches_vrs_with_replicas
            esr_for_each_ranking(spec, vrs_set, vd, n);
            // [] identity ~> [] identity (self)
            leads_to_self_temp(always(identity(n)));
            // Combine: [] (desired /\ identity) ~> [] (current /\ identity)
            always_leads_to_always_combine(
                spec,
                lift_state(conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, n)),
                identity(n),
                lift_state(conjuncted_current_state_matches_vrs_with_replica_diff(vrs_set, vd, n)),
                identity(n)
            );
        }

        // Obligation 2: [] (p_vrs(n) => [] (exists m <= n. p_vrs(m)))
        assert forall |n: nat| #![trigger p_vrs(n)]
            spec.entails(always(p_vrs(n).implies(always(tla_exists(|m: nat| lift_state(|s| m <= n).and(p_vrs(m))))))) by {
            ranking_never_increases(spec, vrs_set, vd, controller_id, cluster, n);
            temp_pred_equality(
                p_vrs(n),
                lift_state(conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, n))
                    .and(lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, n)))
            );
            tla_exists_p_tla_exists_q_equality(
                |m: nat| lift_state(|s| m <= n).and(p_vrs(m)),
                |m: nat| lift_state(|s| m <= n)
                    .and(lift_state(conjuncted_desired_state_is_vrs_with_replica_diff(vrs_set, vd, m))
                    .and(lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set, vd, m))))
            );
        }

        // Obligation 3: n > 0 => [] q_vrs(n) ~> !p_vrs(n)
        assert forall |n: nat| #![trigger p_vrs(n)] n > 0 ==>
            spec.entails(always(q_vrs(n)).leads_to(not(p_vrs(n)))) by {
            if n > 0 {
                ranking_decreases_after_vrs_esr(spec, vrs_set, vd, controller_id, cluster, n);
            }
        }
        leads_to_by_monotonicity3(spec, p_vrs, q_vrs);
        // Now we have: forall n, spec |= p_vrs(n) ~> [] p_vrs(0)

        // [] p_vrs(0) ~> [] q_vrs(0)
        // (already asserted above for n=0)

        // Chain: p_vrs(n_init) ~> [] p_vrs(0) ~> [] q_vrs(0)
        leads_to_trans(spec, p_vrs(n_init), always(p_vrs(0)), always(q_vrs(0)));

        // [] vrs_set_pre entails p_vrs(n_init)
        assert(lifted_always_vrs_set_pre(vrs_set_with_diff).entails(p_vrs(n_init))) by {
            always_entails_current(lift_state(vrs_set_pre(vrs_set_with_diff)));
            temp_pred_equality(
                lifted_always_vrs_set_pre(vrs_set_with_diff),
                always(lift_state(vrs_set_pre(vrs_set_with_diff)))
            );
            assert(lift_state(vrs_set_pre(vrs_set_with_diff)).entails(p_vrs(n_init)));
            entails_trans(
                lifted_always_vrs_set_pre(vrs_set_with_diff),
                lift_state(vrs_set_pre(vrs_set_with_diff)),
                p_vrs(n_init)
            );
        }
        entails_implies_leads_to(spec, lifted_always_vrs_set_pre(vrs_set_with_diff), p_vrs(n_init));
        leads_to_trans(spec, lifted_always_vrs_set_pre(vrs_set_with_diff), p_vrs(n_init), always(q_vrs(0)));

        // spec |= [] stable_vd_post && [] vrs_set_pre ~> [] stable_vd_post && [] q_vrs(0)
        leads_to_self_temp(always(stable_vd_post));
        always_leads_to_always_combine(spec, lift_state(vrs_set_pre(vrs_set_with_diff)), stable_vd_post, q_vrs(0), stable_vd_post);
        always_and_equality(q_vrs(0), stable_vd_post);
        always_and_equality(lift_state(vrs_set_pre(vrs_set_with_diff)), stable_vd_post);

        // [] q_vrs(0) ~> [] composed_post
        // q_vrs(0) includes both identity(0) and current_state_matches(0)
        // With stable_inv, this implies composed_current_state_matches
        let stable_inv = lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id));
        assert forall |ex: Execution<ClusterState>|
            #[trigger] q_vrs(0).and(stable_inv).satisfied_by(ex)
            implies #[trigger] lift_state(composed_current_state_matches(vd)).satisfied_by(ex) by {
            conjuncted_current_state_matches_vrs_with_replica_diff_0_implies_composed(vd, cluster, controller_id, vrs_set, ex.head());
        }
        entails_preserved_by_always(
            q_vrs(0).and(stable_inv),
            lift_state(composed_current_state_matches(vd))
        );
        // always(q_vrs(0)) /\ always(stable_inv) == always(q_vrs(0) /\ stable_inv)
        assert(always(q_vrs(0)).and(always(stable_inv)) == always(q_vrs(0).and(stable_inv))) by {
            always_and_equality(q_vrs(0), stable_inv);
        }
        entails_implies_leads_to(always(stable_vd_post), always(q_vrs(0)).and(always(stable_inv)), lifted_always_composed_post);
        // always(stable_vd_post) |= [] q_vrs(0) ~> [] composed_post
        always_double_equality(stable_inv);
        entails_preserved_by_always(stable_vd_post, stable_inv);
        leads_to_by_borrowing_inv(always(stable_vd_post), always(q_vrs(0)), lifted_always_composed_post, always(stable_inv));

        // true |= [] stable_vd_post && [] q_vrs(0) ~> [] composed_post
        temp_pred_equality(
            true_pred().and(always(stable_vd_post)),
            always(stable_vd_post)
        );
        unpack_conditions_from_spec(
            true_pred(),
            always(stable_vd_post),
            always(q_vrs(0)),
            lifted_always_composed_post,
        );

        // spec |= [] stable_vd_post && [] q_vrs(0) ~> [] composed_post
        temp_pred_equality(
            lifted_always_vrs_set_pre(vrs_set_with_diff),
            always(lift_state(vrs_set_pre(vrs_set_with_diff)))
        );
        always_and_equality(stable_vd_post, lift_state(vrs_set_pre(vrs_set_with_diff)));
        entails_and_different_temp(
            spec,
            true_pred(),
            lifted_always_vrs_set_pre(vrs_set_with_diff).and(always(stable_vd_post)).leads_to(always(q_vrs(0)).and(always(stable_vd_post))),
            always(q_vrs(0)).and(always(stable_vd_post)).leads_to(lifted_always_composed_post),
        );
        temp_pred_equality(spec, spec.and(true_pred()));
        entails_and_temp(spec,
            lifted_always_vrs_set_pre(vrs_set_with_diff).and(always(stable_vd_post)).leads_to(always(q_vrs(0)).and(always(stable_vd_post))),
            always(q_vrs(0)).and(always(stable_vd_post)).leads_to(lifted_always_composed_post),
        );
        leads_to_trans(
            spec,
            lifted_always_vrs_set_pre(vrs_set_with_diff).and(always(stable_vd_post)),
            always(q_vrs(0)).and(always(stable_vd_post)),
            lifted_always_composed_post
        );
    }
    // Extract finiteness from lifted_always_vrs_set_pre to satisfy pre
    // spec |= [] stable_vd_post && \E (vrs_set,n) [] vrs_set_pre(vrs_set_with_diff) ~> [] composed_post
    assert forall |vrs_set_with_diff: (Set<VReplicaSetView>, nat)|
        lifted_always_vrs_set_pre(vrs_set_with_diff).and(always(stable_vd_post)).entails(lift_state(|s: ClusterState| #[trigger] pre(vrs_set_with_diff))) by {
        always_entails_current(lift_state(vrs_set_pre(vrs_set_with_diff)));
        entails_trans_n!(
            lifted_always_vrs_set_pre(vrs_set_with_diff).and(always(stable_vd_post)),
            lifted_always_vrs_set_pre(vrs_set_with_diff),
            lift_state(vrs_set_pre(vrs_set_with_diff)),
            lift_state(current_state_match_vd_applied_to_vrs_set_with_replicas(vrs_set_with_diff.0, vd, vrs_set_with_diff.1)),
            lift_state(|s: ClusterState| #[trigger] pre(vrs_set_with_diff))
        );
    }
    leads_to_exists_intro_with_pre(spec, |vrs_set_with_diff| lifted_always_vrs_set_pre(vrs_set_with_diff).and(always(stable_vd_post)), lifted_always_composed_post, pre);
    tla_exists_and_equality(
        lifted_always_vrs_set_pre,
        always(stable_vd_post)
    );
    // -- Step 5: Chain everything together --
    // spec |= [] desired_state_is ~> [] stable_vd_post
    // [] stable_vd_post |= \E (vrs_set,n) [] vrs_set_pre
    // spec |= \E (vrs_set,n) [] vrs_set_pre ~> [] composed
    // Need: spec |= [] desired_state_is ~> [] composed

    // First: spec |= [] desired_state_is ~> \E (vrs_set,n) [] vrs_set_pre /\ [] stable_vd_post
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

    // Final chain
    leads_to_trans(
        spec,
        always(lift_state(desired_state_is(vd))),
        tla_exists(lifted_always_vrs_set_pre).and(always(stable_vd_post)),
        lifted_always_composed_post
    );
}

}
