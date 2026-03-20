use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::*, message::*};
use crate::reconciler::spec::io::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_lemmas::*, liveness::{spec::*, terminate, resource_match::*, proof::*, api_actions::*, rolling_update::resource_match::*}, predicate::*},
    proof::liveness::rolling_update::predicate as ru_predicate,
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

pub open spec fn conjuncted_desired_state_is_vrs(vrs_set: Set<VReplicaSetView>) -> StatePred<ClusterState> {
    |s: ClusterState| (forall |vrs| #[trigger] vrs_set.contains(vrs) ==> vrs_liveness::desired_state_is(vrs)(s))
}

pub open spec fn conjuncted_current_state_matches_vrs(vrs_set: Set<VReplicaSetView>) -> StatePred<ClusterState> {
    |s: ClusterState| (forall |vrs| #[trigger] vrs_set.contains(vrs) ==> vrs_liveness::current_state_matches(vrs)(s))
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

pub open spec fn desired_state_is_vrs_with_key(vrs: VReplicaSetView, vrs_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& vrs_liveness::desired_state_is(vrs)(s)
        &&& vrs.object_ref() == vrs_key
    }
}

pub open spec fn desired_state_is_vrs_with_replicas_diff_and_key(vd: VDeploymentView, vrs: VReplicaSetView, vrs_key: ObjectRef, diff: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& vrs_liveness::desired_state_is(vrs)(s)
        &&& replicas_diff(vd, vrs) == diff
        &&& vrs.object_ref() == vrs_key
    }
}

pub open spec fn current_state_matches_vrs_with_key(vrs: VReplicaSetView, vrs_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& vrs_liveness::current_state_matches(vrs)(s)
        &&& vrs.object_ref() == vrs_key
    }
}

pub open spec fn current_state_matches_vrs_with_replicas_diff_and_key(vd: VDeploymentView, vrs: VReplicaSetView, vrs_key: ObjectRef, diff: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& vrs_liveness::current_state_matches(vrs)(s)
        &&& replicas_diff(vd, vrs) == diff
        &&& vrs.object_ref() == vrs_key
    }
}

// Strip resource_version AND status for vrs_set identity stability.
// When VD controller changes replicas via GetThenUpdate, or VRS controller changes status,
// the mapped set remains the same.
// spec.replicas is passed as argument in higher level predicates
pub open spec fn vrs_with_no_rv_status(vrs: VReplicaSetView) -> VReplicaSetView {
    VReplicaSetView {
        metadata: vrs.metadata.without_resource_version(),
        status: None,
        ..vrs
    }
}

pub open spec fn is_old_vrs_of(vrs: VReplicaSetView, vd: VDeploymentView, new_vrs_key: ObjectRef) -> bool {
    valid_owned_vrs(vrs, vd) && vrs.object_ref() != new_vrs_key
}

pub open spec fn old_vrs_set_is_owned_by_vd(vrs_set: Set<VReplicaSetView>, vd: VDeploymentView, new_vrs_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& vrs_set == s.resources().values()
            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
            .filter(|vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key))
            .map(|vrs: VReplicaSetView| vrs_with_no_rv_status(vrs))
        &&& vrs_set.finite()
    }
}

// *** Obligation proofs for leads_to_by_monotonicity3 (per fixed vrs_set) ***

// Obligation 1: ESR for each ranking level
// spec |= [] desired_vrs ~> [] matches_vrs
pub proof fn esr_for_each_ranking(
    spec: TempPred<ClusterState>, vrs_set: Set<VReplicaSetView>, vd: VDeploymentView, new_vrs_key: ObjectRef
)
    requires
        spec.entails(vrs_liveness::vrs_eventually_stable_reconciliation()),
    ensures
        spec.entails(
            always(lift_state(conjuncted_desired_state_is_vrs(vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key))))
        .leads_to(
            always(lift_state(conjuncted_current_state_matches_vrs(vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key)))))),
{
    if !vrs_set.finite() {
        // old_vrs_set_is_owned_by_vd requires finite(), so the pre is unsatisfiable
        temp_pred_equality(
            lift_state(conjuncted_desired_state_is_vrs(vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key))),
            false_pred::<ClusterState>()
        );
        false_is_stable::<ClusterState>();
        stable_to_always::<ClusterState>(false_pred());
        false_leads_to_anything(spec,
            always(lift_state(conjuncted_current_state_matches_vrs(vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key))))
        );
        return;
    }
    // Instantiate VRS ESR for each vrs in the set
    assert forall |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs) implies
        spec.entails(always(lift_state(vrs_liveness::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs))))) by {
        tla_forall_p_tla_forall_q_equality(
            |vrs| vrs_liveness::vrs_eventually_stable_reconciliation_per_cr(vrs),
            |vrs| always(lift_state(vrs_liveness::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs))))
        );
        use_tla_forall(spec, |vrs| always(lift_state(vrs_liveness::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))), vrs);
    }
    // Compose individual VRS ESRs into the conjuncted form
    let desired_state_is_vrs = |vrs| vrs_liveness::desired_state_is(vrs);
    let current_state_matches_vrs = |vrs| vrs_liveness::current_state_matches(vrs);
    assert(conjuncted_desired_state_is_vrs(vrs_set)
        == |s: ClusterState| (forall |vrs| #[trigger] vrs_set.contains(vrs) ==> desired_state_is_vrs(vrs)(s)));
    assert(conjuncted_current_state_matches_vrs(vrs_set)
        == |s: ClusterState| (forall |vrs| #[trigger] vrs_set.contains(vrs) ==> current_state_matches_vrs(vrs)(s)));
    spec_entails_always_tla_forall_leads_to_always_tla_forall_within_domain(
        spec, desired_state_is_vrs, current_state_matches_vrs, vrs_set,
        conjuncted_desired_state_is_vrs(vrs_set), conjuncted_current_state_matches_vrs(vrs_set)
    );
    // Combine with self-leads-to for owned
    leads_to_self_temp(always(lift_state(old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key))));
    always_leads_to_always_combine(spec,
        lift_state(conjuncted_desired_state_is_vrs(vrs_set)),
        lift_state(old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key)),
        lift_state(conjuncted_current_state_matches_vrs(vrs_set)),
        lift_state(old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key))
    );
}

// Obligation 2: Monotonicity (ranking never increases)
// forall n. spec |= [] (p(n) => [] (exists m <= n. p(m)))
#[verifier(rlimit(50))]
#[verifier(spinoff_prover)]
pub proof fn ranking_never_increases(
    spec: TempPred<ClusterState>, new_vrs: VReplicaSetView, new_vrs_key: ObjectRef, vd: VDeploymentView, controller_id: int, cluster: Cluster
)
    requires
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
        spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
        spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    ensures
        forall |n| spec.entails(always(lift_state(#[trigger] desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, n))
            .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
        .implies(always(tla_exists(|m: nat| lift_state(|s| m <= n).and(
            lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))))
        ))))),
{
    // use next_monotonic_to_always_exists
    let p = |n: nat| and!(
        desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, n),
        inductive_current_state_matches(vd, controller_id, new_vrs_key)
    );
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s_prime)
        &&& vd_rely_condition(cluster, controller_id)(s)
        &&& vd_rely_condition(cluster, controller_id)(s_prime)
    };
    always_to_always_later(spec, lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)));
    always_to_always_later(spec, lifted_vd_reconcile_request_only_interferes_with_itself(controller_id));
    always_to_always_later(spec, lifted_vd_rely_condition(cluster, controller_id));
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
        later(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))),
        lifted_vd_reconcile_request_only_interferes_with_itself(controller_id),
        later(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)),
        lifted_vd_rely_condition(cluster, controller_id),
        later(lifted_vd_rely_condition(cluster, controller_id))
    );
    assert forall |n: nat| lift_state(p(n)) == lift_state(#[trigger] desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, n))
        .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))) by {
        and_eq(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, n), inductive_current_state_matches(vd, controller_id, new_vrs_key));
    }
    // pre, inv is preserved
    assert forall |n| #![trigger p(n)] forall |s, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) && p(n)(s) ==> exists |m: nat| m <= n && #[trigger] p(m)(s_prime) by {
        // #![trigger p(m)] reduce the flakiness here in a strange way
        assert forall |s, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) && p(n)(s) implies exists |m: nat| #![trigger p(m)] m <= n && #[trigger] p(m)(s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    let msg = input->0;
                    if msg.src == HostId::Controller(controller_id, vd.object_ref()) {
                        if req_msg_is_scale_new_vrs_req(vd, controller_id, msg, (new_vrs.metadata.uid->0, new_vrs_key))(s) {
                            ranking_never_increases_from_s_to_s_prime(vd, controller_id, cluster, s, s_prime, new_vrs, new_vrs_key, n, msg);
                        } else {
                            assert(req_msg_is_list_vrs_req(vd, controller_id, msg, s)); // read-only
                            assert(s_prime.resources() == s.resources());
                            assert(p(n)(s_prime));
                        }
                    } else {
                        assume(false); // api_action::other_requests_maintains_vrs_set_and_conjuncted_desired_state_is_vrs
                    }
                },
                _ => {
                    assert(s_prime.resources() == s.resources());
                    assert(p(n)(s_prime));
                }
            }
        }
    }
    assert forall |n: nat| spec.entails(always(lift_state(#[trigger] p(n)).implies(always(tla_exists(|m: nat| lift_state(|s| m <= n).and(lift_state(p(m)))))))) by {
        next_monotonic_to_always_exists(spec, stronger_next, p);
    }
    assert forall |n| spec.entails(always(lift_state(#[trigger] desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, n))
        .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
    .implies(always(tla_exists(|m: nat| lift_state(|s| m <= n)
        .and(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m))
        .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))))
    ))))) by {
        tla_exists_p_tla_exists_q_equality(
            |m: nat| lift_state(|s| m <= n).and(lift_state(p(m))),
            |m: nat| lift_state(|s| m <= n)
                .and(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m))
                .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))))
        );
    }
}

#[verifier(external_body)]
proof fn ranking_never_increases_from_s_to_s_prime(
    vd: VDeploymentView, controller_id: int, cluster: Cluster, s: ClusterState, s_prime: ClusterState, new_vrs: VReplicaSetView, new_vrs_key: ObjectRef, n: nat, req_msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime),
    forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s),
    forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s_prime),
    vd_rely_condition(cluster, controller_id)(s),
    vd_rely_condition(cluster, controller_id)(s_prime),
    inductive_current_state_matches(vd, controller_id, new_vrs_key)(s),
    desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, n)(s),
    req_msg.src == HostId::Controller(controller_id, vd.object_ref()),
    req_msg_is_scale_new_vrs_req(vd, controller_id, req_msg, (new_vrs.metadata.uid->0, new_vrs_key))(s)
ensures
    exists |m: nat| #![trigger desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m)] m <= n
        && desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m)(s_prime)
        && inductive_current_state_matches(vd, controller_id, new_vrs_key)(s_prime),
{}

// Obligation 3: Ranking decrease
// forall n > 0. spec |= [] q(n) ~> !p(n)
// Prove with a specialized version of ESR proof with spec |= [] current_state_matches
#[verifier(external_body)]
pub proof fn ranking_decreases_after_vrs_esr(
    spec: TempPred<ClusterState>, vd: VDeploymentView, controller_id: int, cluster: Cluster, new_vrs: VReplicaSetView, new_vrs_key: ObjectRef, diff: nat
)
    requires
        diff > 0,
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
        spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
        spec.entails(tla_forall((|i| cluster.external_next().weak_fairness((controller_id, i))))),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        valid(stable(spec)),
    ensures
        spec.entails(always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)).and(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff))))
            .leads_to(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)).and(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff))))),
{
    // 0. unpack invariants from cluster_invariants_since_reconciliation
    entails_always_unpack_n!(spec,
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
        lift_state(helper_invariants::vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)),
        lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(desired_state_is(vd))
    );
    always_to_always_later(spec, lift_state(desired_state_is(vd)));
    // 1. termination, true ~> reconcile_idle
    // same as lemma_true_leads_to_always_current_state_matches
    let reconcile_idle = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
    };
    assume(spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))));
    assert(spec.entails(true_pred().leads_to(lift_state(reconcile_idle)))) by {
        assume(false); // TODO: compose other inv in addition to cluster_invariants_since_reconciliation
        terminate::reconcile_eventually_terminates(spec, cluster, controller_id);
        use_tla_forall(spec, |key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))), vd.object_ref());
    }
    // reconcile_idle ~> reconcile_scheduled
    let reconcile_scheduled = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
        &&& s.scheduled_reconciles(controller_id).contains_key(vd.object_ref())
    };
    assert(spec.entails(lift_state(reconcile_idle).leads_to(lift_state(reconcile_scheduled)))) by {
        let input = vd.object_ref();
        let stronger_reconcile_idle = |s: ClusterState| {
            &&& !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
            &&& !s.scheduled_reconciles(controller_id).contains_key(vd.object_ref())
        };
        let stronger_next = |s, s_prime| {
            &&& cluster.next()(s, s_prime)
            &&& desired_state_is(vd)(s)
            &&& desired_state_is(vd)(s_prime)
        };
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(desired_state_is(vd)),
            later(lift_state(desired_state_is(vd)))
        );
        cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(
            spec, controller_id, input, stronger_next, and!(stronger_reconcile_idle, desired_state_is(vd)), reconcile_scheduled
        );
        temp_pred_equality(
            lift_state(stronger_reconcile_idle).and(lift_state(desired_state_is(vd))),
            lift_state(and!(stronger_reconcile_idle, desired_state_is(vd)))
        );
        leads_to_by_borrowing_inv(spec, lift_state(stronger_reconcile_idle), lift_state(reconcile_scheduled), lift_state(desired_state_is(vd)));
        entails_implies_leads_to(spec, lift_state(reconcile_scheduled), lift_state(reconcile_scheduled));
        or_leads_to_combine(spec, lift_state(stronger_reconcile_idle), lift_state(reconcile_scheduled), lift_state(reconcile_scheduled));
        temp_pred_equality(lift_state(stronger_reconcile_idle).or(lift_state(reconcile_scheduled)), lift_state(reconcile_idle));
    }
    let init = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Init]),
        no_pending_req_in_cluster(vd, controller_id)
    );
    // 2. reconcile_idle ~> init
    assert(spec.entails(lift_state(reconcile_scheduled).leads_to(lift_state(init)))) by {
        let input = (None, Some(vd.object_ref()));
        let stronger_next = |s, s_prime| {
            &&& cluster.next()(s, s_prime) 
            &&& Cluster::crash_disabled(controller_id)(s) 
            &&& Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s) 
            &&& helper_invariants::vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)(s_prime) 
            &&& Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)(s_prime)
        };
        always_to_always_later(spec, lift_state(helper_invariants::vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)));
        always_to_always_later(spec, lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)));
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(Cluster::crash_disabled(controller_id)),
            lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
            later(lift_state(helper_invariants::vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id))),
            later(lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)))
        );
        assert forall |s, s_prime| reconcile_scheduled(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies init(s_prime) by {
            VDeploymentReconcileState::marshal_preserves_integrity();
            lemma_cr_fields_eq_to_cr_predicates_eq(vd, controller_id, s_prime);
        }
        cluster.lemma_pre_leads_to_post_by_controller(
            spec, controller_id, input, stronger_next, ControllerStep::RunScheduledReconcile, reconcile_scheduled, init
        );
    }
    // 3. init ~> after_list ~> after_scale_new_vrs ~> !desired_state_is
    let pre = lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)).and(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff)));
    let post = lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)).and(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff)));
    assert(spec.entails(always(pre).leads_to(lift_state(init).and(always(pre))))) by {
        leads_to_trans_n!(
            spec, true_pred(), lift_state(reconcile_idle), lift_state(reconcile_scheduled), lift_state(init)
        );
        leads_to_with_always(spec, true_pred(), lift_state(init), pre);
        temp_pred_equality(true_pred().and(always(pre)), always(pre));
    }
    assert(spec.entails(lift_state(init).and(always(pre)).leads_to(post))) by {
        // convert preconditions
        entails_trans(spec.and(always(pre)), spec, always(lift_action(cluster.next())));
        entails_trans(spec.and(always(pre)), spec, always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)));
        entails_trans(spec.and(always(pre)), spec, always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))));
        entails_trans(spec.and(always(pre)), spec, always(lifted_vd_rely_condition(cluster, controller_id)));
        entails_trans(spec.and(always(pre)), spec, always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))));
        entails_trans(spec.and(always(pre)), spec, tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1))));
        entails_trans(spec.and(always(pre)), spec, tla_forall(|i| cluster.api_server_next().weak_fairness(i)));
        entails_trans(spec.and(always(pre)), spec, tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i)));
        entails_trans(spec.and(always(pre)), spec, tla_forall((|i| cluster.external_next().weak_fairness((controller_id, i)))));
        entails_trans(spec.and(always(pre)), spec, tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i))));
        // lemma_from_init_to_not_desired_state_is(vd, spec.and(always(pre)), cluster, controller_id, diff);

        always_p_is_stable(pre);
        unpack_conditions_from_spec(spec, always(pre), lift_state(init), post);
    }
    leads_to_trans(spec, always(pre), lift_state(init).and(always(pre)), post);
}

// From inductive_current_state_matches, extract (vrs_set, n) witness
#[verifier(spinoff_prover)]
pub proof fn current_state_match_vd_implies_exists_old_vrs_set(
    vd: VDeploymentView, cluster: Cluster, controller_id: int, new_vrs_key: ObjectRef, s: ClusterState
) -> (vrs_set: Set<VReplicaSetView>) // vrs_set, new_vrs, replicas_diff
    requires
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
        current_state_matches_with_new_vrs_key(vd, new_vrs_key)(s),
    ensures
        old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key)(s),
        conjuncted_desired_state_is_vrs(vrs_set)(s),
{
    let vrs_set = s.resources().values()
        .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
        .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
        .filter(|vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key))
        .map(|vrs: VReplicaSetView| vrs_with_no_rv_status(vrs));
    assert(vrs_set.finite()) by {
        lemma_values_finite(s.resources());
        finite_set_to_finite_filtered_set(s.resources().values(), |obj: DynamicObjectView| obj.kind == VReplicaSetView::kind());
        s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .lemma_map_finite(|obj: DynamicObjectView| VReplicaSetView::unmarshal(obj)->Ok_0);
        finite_set_to_finite_filtered_set(
            s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
                .map(|obj: DynamicObjectView| VReplicaSetView::unmarshal(obj)->Ok_0),
            |vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key)
        );
        s.resources().values()
            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
            .filter(|vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key))
            .lemma_map_finite(|vrs: VReplicaSetView| vrs_with_no_rv_status(vrs));
    }
    // |= conjuncted_desired_state_is_vrs(vrs_set)(s)
    VReplicaSetView::marshal_preserves_integrity();
    assert forall |vrs| #[trigger] vrs_set.contains(vrs) implies vrs_liveness::desired_state_is(vrs)(s) by {
        VReplicaSetView::marshal_preserves_integrity();
        let etcd_obj = choose |obj: DynamicObjectView| #[trigger] s.resources().values().contains(obj) && obj.object_ref() == vrs.object_ref();
        let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
        assert(exists |vrs_with_rv_status| vrs_with_no_rv_status(vrs_with_rv_status) == vrs
            && s.resources().values()
            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
            .filter(|vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key)).contains(vrs_with_rv_status));
        let vrs_with_rv_status = choose |vrs_with_rv_status| vrs_with_no_rv_status(vrs_with_rv_status) == vrs
            && s.resources().values()
            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
            .filter(|vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key)).contains(vrs_with_rv_status);
        assert(s.resources().values()
            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0).contains(vrs_with_rv_status));
        assert(exists |etcd_obj| #![trigger s.resources().values().contains(etcd_obj)]
            VReplicaSetView::unmarshal(etcd_obj)->Ok_0 == vrs_with_rv_status
            && s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(etcd_obj));
        let etcd_obj2 = choose |etcd_obj| #![trigger s.resources().values().contains(etcd_obj)]
            VReplicaSetView::unmarshal(etcd_obj)->Ok_0 == vrs_with_rv_status
            && s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(etcd_obj);
        assert(etcd_obj2.object_ref() == vrs.object_ref());
        assert(etcd_obj2 == etcd_obj);
        assert(vrs_liveness::desired_state_is(etcd_vrs)(s));
    }
    assert({
        &&& vrs_set == s.resources().values()
            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
            .filter(|vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key))
            .map(|vrs: VReplicaSetView| vrs_with_no_rv_status(vrs))
        &&& vrs_set.finite()
    });
    return vrs_set;
}

// q(0) with vrs_set identity implies composed_current_state_matches
pub proof fn conjuncted_current_state_matches_old_vrs_0_implies_composed(
    vd: VDeploymentView, cluster: Cluster, controller_id: int, vrs_set: Set<VReplicaSetView>, new_vrs: VReplicaSetView, new_vrs_key: ObjectRef, s: ClusterState
)
    requires
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
        conjuncted_current_state_matches_vrs(vrs_set)(s),
        inductive_current_state_matches(vd, controller_id, new_vrs_key)(s),
        current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0)(s),
        old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key)(s),
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
                assert(vrs_set.contains(vrs_with_no_rv_status(havoc_vrs))) by {
                    let etcd_obj = s.resources()[havoc_vrs.object_ref()];
                    assert(s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(etcd_obj));
                    let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
                    assert(s.resources().values()
                        .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
                        .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
                        .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd))
                        .contains(etcd_vrs));
                    assert(vrs_with_no_rv_status(havoc_vrs) == vrs_with_no_rv_status(etcd_vrs));
                }
                assert(exists |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs) 
                    && vrs_with_no_rv_status(vrs) == vrs_with_no_rv_status(havoc_vrs) && vrs != new_vrs);
                let havoc_vrs_in_set = choose |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs)
                    && vrs_with_no_rv_status(vrs) == vrs_with_no_rv_status(havoc_vrs) && vrs != new_vrs;
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
                assert(vrs_set.map(|vrs: VReplicaSetView| vrs_with_no_rv_status(vrs)).contains(vrs_with_no_rv_status(new_vrs)));
                let mapped_vrs_set_in_etcd = s.resources().values()
                    .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
                    .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
                    .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd))
                    .map(|vrs: VReplicaSetView| vrs_with_no_rv_status(vrs));
                assert(exists |vrs: VReplicaSetView| #[trigger] mapped_vrs_set_in_etcd.contains(vrs) && vrs == vrs_with_no_rv_status(new_vrs));
                let mapped_new_vrs_in_etcd = choose |vrs: VReplicaSetView| #[trigger] mapped_vrs_set_in_etcd.contains(vrs) && vrs == vrs_with_no_rv_status(new_vrs);
                let vrs_set_in_etcd = s.resources().values()
                    .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
                    .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
                    .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd));
                assert(exists |vrs: VReplicaSetView| #[trigger] vrs_set_in_etcd.contains(vrs) && vrs_with_no_rv_status(vrs) == mapped_new_vrs_in_etcd);
                let new_vrs_in_etcd = choose |vrs: VReplicaSetView| #[trigger] vrs_set_in_etcd.contains(vrs) && vrs_with_no_rv_status(vrs) == mapped_new_vrs_in_etcd;
                assert(vrs_with_no_rv_status(new_vrs_in_etcd) == vrs_with_no_rv_status(new_vrs));
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
// TODO: deprecate this
#[verifier(external_body)] // trivial
pub proof fn rolling_update_desired_state_preserves_from_s_to_s_prime(
    vd: VDeploymentView, controller_id: int, cluster: Cluster, vrs_set: Set<VReplicaSetView>, new_vrs_key: ObjectRef, n: nat, s: ClusterState, s_prime: ClusterState
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
        inductive_current_state_matches(vd, controller_id, new_vrs_key)(s),
        inductive_current_state_matches(vd, controller_id, new_vrs_key)(s_prime),
        old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key)(s),
        conjuncted_desired_state_is_vrs(vrs_set)(s),
    ensures
        old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key)(s_prime),
        conjuncted_desired_state_is_vrs(vrs_set)(s_prime),
{}

// *** Top-level rolling update ESR composition theorem ***
pub proof fn rolling_update_leads_to_composed_current_state_matches_vd(
    provided_spec: TempPred<ClusterState>, vd: VDeploymentView, controller_id: int, cluster: Cluster
)
    requires
        // environment invariants
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        provided_spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
        provided_spec.entails(always(lift_action(cluster.next()))),
        // ESR for vrs
        provided_spec.entails(vrs_liveness::vrs_eventually_stable_reconciliation()),
        // ESR for vd (with rolling update behavior)
        provided_spec.entails(always(lift_state(desired_state_is(vd))).leads_to(tla_exists(|new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))))),
        // vd rely
        provided_spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    ensures
        provided_spec.and(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))).entails(always(lift_state(desired_state_is(vd))).leads_to(always(lift_state(composed_current_state_matches(vd))))),
{
    let spec = provided_spec.and(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))));
    entails_trans(spec, provided_spec, always(lift_state(desired_state_is(vd))).leads_to(tla_exists(|new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))))));
    entails_trans(spec, provided_spec, always(lift_action(cluster.next())));
    entails_trans(spec, provided_spec, always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)));
    entails_trans(spec, provided_spec, always(lifted_vd_rely_condition(cluster, controller_id)));
    entails_trans(spec, provided_spec, vrs_liveness::vrs_eventually_stable_reconciliation());
    // Prove: 1. vrs_eventually_stable_reconciliation == \A vrs, [] desired_state_is(vrs) ~> [] current_state_matches(vrs)
    // 2. valid(stable(vrs_eventually_stable_reconciliation))
    assert(vrs_liveness::vrs_eventually_stable_reconciliation() ==
        tla_forall(|vrs| always(lift_state(vrs_liveness::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))))) by
    {
        temp_pred_equality(
            tla_forall(|vrs| vrs_liveness::vrs_eventually_stable_reconciliation_per_cr(vrs)),
            vrs_liveness::vrs_eventually_stable_reconciliation()
        );
        assert forall |vrs| #[trigger] vrs_liveness::vrs_eventually_stable_reconciliation_per_cr(vrs)
            == always(lift_state(vrs_liveness::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))) by {
            temp_pred_equality(
                always(lift_state(vrs_liveness::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))),
                vrs_liveness::vrs_eventually_stable_reconciliation_per_cr(vrs)
            );
        }
        tla_forall_p_tla_forall_q_equality(
            |vrs| vrs_liveness::vrs_eventually_stable_reconciliation_per_cr(vrs),
            |vrs| always(lift_state(vrs_liveness::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs))))
        );
    }
    // [] VRS ESR == VRS ESR
    assert(valid(stable(tla_forall(|vrs| always(lift_state(vrs_liveness::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))))))) by {
        let vrs_to_desired_state = |vrs| always(lift_state(vrs_liveness::desired_state_is(vrs)));
        let vrs_to_current_state = |vrs| always(lift_state(vrs_liveness::current_state_matches(vrs)));
        tla_forall_a_p_a_leads_to_q_a_is_stable(vrs_to_desired_state, vrs_to_current_state);
        assert forall |vrs| #[trigger] vrs_to_desired_state(vrs).leads_to(vrs_to_current_state(vrs))
            == always(lift_state(vrs_liveness::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))) by {
            temp_pred_equality(
                always(lift_state(vrs_liveness::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))),
                vrs_to_desired_state(vrs).leads_to(vrs_to_current_state(vrs))
            );
        }
        tla_forall_p_tla_forall_q_equality(
            |vrs| vrs_to_desired_state(vrs).leads_to(vrs_to_current_state(vrs)),
            |vrs| always(lift_state(vrs_liveness::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs))))
        );
    }
    stable_to_always(tla_forall(|vrs| always(lift_state(vrs_liveness::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs))))));
    stable_to_always(vrs_liveness::vrs_eventually_stable_reconciliation());

    assert forall |new_vrs_key: ObjectRef| spec.entails(always(lift_state(#[trigger] inductive_current_state_matches(vd, controller_id, new_vrs_key))).leads_to(always(lift_state(composed_current_state_matches(vd))))) by {
        // old vrs track
        // spec |= [] inductive_current_state_matches |= \E vrs_set []
        let p = always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)));
        let all_vrs_post = |ov_set_nv: (Set<VReplicaSetView>, VReplicaSetView)|
            always(lift_state(conjuncted_current_state_matches_vrs(ov_set_nv.0)).and(lift_state(old_vrs_set_is_owned_by_vd(ov_set_nv.0, vd, new_vrs_key))))
            .and(always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, ov_set_nv.1, new_vrs_key, 0)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))));
        let composed_vd_post = always(lift_state(composed_current_state_matches(vd)));
        assert(spec.entails(always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
            .leads_to(tla_exists(|old_vrs_set| always(lift_state(conjuncted_current_state_matches_vrs(old_vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(old_vrs_set, vd, new_vrs_key)))))))) by {
            assert(always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))).entails(
                tla_exists(|old_vrs_set| always(lift_state(conjuncted_desired_state_is_vrs(old_vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(old_vrs_set, vd, new_vrs_key))))))) by {
                // 1. inductive_current_state_matches |= \E vrs_set []
                // 2. valid(stable) vrs_set
                assume(false);
            }
            entails_implies_leads_to(spec,
                always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))),
                tla_exists(|old_vrs_set| always(lift_state(conjuncted_desired_state_is_vrs(old_vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(old_vrs_set, vd, new_vrs_key)))))
            );
            assert forall |old_vrs_set| spec.entails(always(lift_state(conjuncted_desired_state_is_vrs(old_vrs_set)).and(lift_state(#[trigger] old_vrs_set_is_owned_by_vd(old_vrs_set, vd, new_vrs_key))))
                .leads_to(always(lift_state(conjuncted_current_state_matches_vrs(old_vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(old_vrs_set, vd, new_vrs_key)))))) by {
                esr_for_each_ranking(spec, old_vrs_set, vd, new_vrs_key);
            }
            leads_to_exists_intro2(spec,
                |old_vrs_set| always(lift_state(conjuncted_desired_state_is_vrs(old_vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(old_vrs_set, vd, new_vrs_key)))),
                |old_vrs_set| always(lift_state(conjuncted_current_state_matches_vrs(old_vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(old_vrs_set, vd, new_vrs_key))))
            );
            leads_to_trans(spec,
                always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))),
                tla_exists(|old_vrs_set| always(lift_state(conjuncted_desired_state_is_vrs(old_vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(old_vrs_set, vd, new_vrs_key))))),
                tla_exists(|old_vrs_set| always(lift_state(conjuncted_current_state_matches_vrs(old_vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(old_vrs_set, vd, new_vrs_key)))))
            );
        }
        // new vrs track
        // spec |= [] inductive_current_state_matches ~> \E new_vrs []
        assert(spec.entails(always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
            .leads_to(tla_exists(|new_vrs: VReplicaSetView| always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))))))) by {
            // inductive_current_state_matches |= \E new_vrs desired(new_vrs)
            assert(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)).entails(tla_exists(|new_vrs: VReplicaSetView| lift_state(desired_state_is_vrs_with_key(new_vrs, new_vrs_key))))) by {
                assume(false);
            }
            assert(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))
                == tla_exists(|new_vrs: VReplicaSetView| lift_state(desired_state_is_vrs_with_key(new_vrs, new_vrs_key)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))))) by {
                simplify_predicate(
                    lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)),
                    tla_exists(|new_vrs: VReplicaSetView| lift_state(desired_state_is_vrs_with_key(new_vrs, new_vrs_key)))
                );
                temp_pred_equality(
                    lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)).and(tla_exists(|new_vrs: VReplicaSetView| lift_state(desired_state_is_vrs_with_key(new_vrs, new_vrs_key)))),
                    tla_exists(|new_vrs: VReplicaSetView| lift_state(desired_state_is_vrs_with_key(new_vrs, new_vrs_key))).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
                );
                let a_to_p = |new_vrs| lift_state(desired_state_is_vrs_with_key(new_vrs, new_vrs_key));
                let q = lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key));
                tla_exists_p_tla_exists_q_equality(
                    |new_vrs| a_to_p(new_vrs).and(q),
                    |new_vrs| lift_state(desired_state_is_vrs_with_key(new_vrs, new_vrs_key)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
                );
                // fix reasoning on predicate equality
                tla_exists_and_equality(a_to_p, q);
            }
            // inductive_current_state_matches == (\E new_vrs desired(new_vrs)) /\ inductive_current_state_matches == \E new_vrs (desired(new_vrs) /\ inductive_current_state_matches)
            // \A new_vrs inductive_current_state_matches /\ desired(new_vrs) ~> [] match(new_vrs)
            assert forall |new_vrs: VReplicaSetView| spec.entails(lift_state(desired_state_is_vrs_with_key(new_vrs, new_vrs_key)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
                .leads_to(always(lift_state(#[trigger] current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0))))) by {
                let p = |diff: nat| lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)));
                let q = |diff: nat| lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)));
                // by leads_to_by_monotonicity3
                // we need inductive_current_state_matches with the key here
                // 1. forall |n| #![trigger p(n)] spec.entails(always(p(n)).leads_to(always(q(n)))),
                assert forall |n: nat| #![trigger p(n)] spec.entails(always(p(n)).leads_to(always(q(n)))) by {
                    assume(false);
                }
                // 2. forall |n| #![trigger p(n)] spec.entails(always(p(n).implies(always(tla_exists(|m: nat| lift_state(|s| m <= n).and(p(m))))))),
                assert forall |n: nat| #![trigger p(n)] spec.entails(always(p(n).implies(always(tla_exists(|m: nat| lift_state(|s| m <= n).and(p(m))))))) by {
                    ranking_never_increases(spec, new_vrs, new_vrs_key, vd, controller_id, cluster);
                    temp_pred_equality(
                        lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, n))
                            .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))),
                        p(n)
                    );
                    tla_exists_p_tla_exists_q_equality(
                        |m: nat| lift_state(|s| m <= n).and(
                            lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))),
                        |m: nat| lift_state(|s| m <= n).and(p(m))
                    );
                }
                // 3. forall |n: nat| #![trigger p(n)] n > 0 ==> spec.entails(always(q(n)).leads_to(not(p(n)))),
                assert forall |n: nat| #![trigger p(n)] n > 0 implies spec.entails(always(q(n)).leads_to(not(p(n)))) by {
                    assume(false);
                }
                leads_to_by_monotonicity3(spec, p, q);
                // leads_to_transitivity
                leads_to_exists_intro(spec, p, always(q(0)));
                assert(lift_state(desired_state_is_vrs_with_key(new_vrs, new_vrs_key)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))).entails(tla_exists(p))) by {
                    assume(false);
                }
                entails_implies_leads_to(spec,
                    lift_state(desired_state_is_vrs_with_key(new_vrs, new_vrs_key)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))),
                    tla_exists(p)
                );
                entails_preserved_by_always(
                    q(0),
                    lift_state(#[trigger] current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0))
                );
                entails_implies_leads_to(spec,
                    always(q(0)),
                    always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0)))
                );
                leads_to_trans_n!(spec,
                    lift_state(desired_state_is_vrs_with_key(new_vrs, new_vrs_key)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))),
                    tla_exists(p),
                    always(q(0)),
                    always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0)))
                );
            }
            leads_to_exists_intro2(spec,
                |new_vrs: VReplicaSetView| lift_state(desired_state_is_vrs_with_key(new_vrs, new_vrs_key)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))),
                |new_vrs: VReplicaSetView| always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0)))
            );
            always_entails_current(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)));
            entails_implies_leads_to(spec,
                always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))),
                lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))
            );
            leads_to_trans(spec,
                always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))),
                lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)),
                tla_exists(|new_vrs: VReplicaSetView| always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0))))
            );
            leads_to_self_temp(
                always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
            );
            // add inductive_csm to post
            tla_exists_p_tla_exists_q_equality(
                |new_vrs: VReplicaSetView| always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0))),
                |new_vrs: VReplicaSetView| always((|new_vrs: VReplicaSetView| lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0)))(new_vrs))
            );
            // fix reasoning on predicate equality
            let p = lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key));
            let a_to_q = |new_vrs| lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0));
            tla_exists_p_tla_exists_q_equality(
                |new_vrs| always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))),
                |new_vrs| always(a_to_q(new_vrs).and(p))
            );
            assert(spec.entails(always(p).leads_to(tla_exists(|new_vrs| always(a_to_q(new_vrs).and(p)))))) by {
                leads_to_exists_always_combine(spec, always(p), a_to_q, lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)));
            }
        }
        // \E vrs_set [] /\ \E new_vrs [] ~> \E (vrs_set and new_vrs) []
        assert(spec.entails(p.leads_to(tla_exists(all_vrs_post)))) by {
            let old_vrs_post = |old_vrs_set| lift_state(conjuncted_current_state_matches_vrs(old_vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(old_vrs_set, vd, new_vrs_key)));
            let new_vrs_post = |new_vrs| lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)));
            tla_exists_p_tla_exists_q_equality(
                |old_vrs_set| always(old_vrs_post(old_vrs_set)),
                |old_vrs_set| always(lift_state(conjuncted_current_state_matches_vrs(old_vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(old_vrs_set, vd, new_vrs_key))))
            );
            tla_exists_p_tla_exists_q_equality(
                |new_vrs| always(new_vrs_post(new_vrs)),
                |new_vrs| always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))))
            );
            leads_to_exists_always_combine2(spec, p, old_vrs_post, new_vrs_post);
            assert forall |ov_set_nv: (Set<VReplicaSetView>, VReplicaSetView)| #[trigger] all_vrs_post(ov_set_nv)
                == (|ov_set_nv: (Set<VReplicaSetView>, VReplicaSetView)| always(old_vrs_post(ov_set_nv.0)).and(always(new_vrs_post(ov_set_nv.1))))(ov_set_nv) by {
                temp_pred_equality(
                    all_vrs_post(ov_set_nv),
                    always(old_vrs_post(ov_set_nv.0)).and(always(new_vrs_post(ov_set_nv.1)))
                );
            }
            tla_exists_p_tla_exists_q_equality(
                all_vrs_post,
                |ov_set_nv: (Set<VReplicaSetView>, VReplicaSetView)| always(old_vrs_post(ov_set_nv.0)).and(always(new_vrs_post(ov_set_nv.1)))
            );
        }
        // \A [] old_vrs_set and [] new_vrs ~> [] composed_current_state_matches
        assert forall |ov_set_nv: (Set<VReplicaSetView>, VReplicaSetView)| #![trigger all_vrs_post(ov_set_nv)] spec.entails(all_vrs_post(ov_set_nv).leads_to(composed_vd_post)) by {
            always_and_equality(
                lift_state(conjuncted_current_state_matches_vrs(ov_set_nv.0)),
                lift_state(old_vrs_set_is_owned_by_vd(ov_set_nv.0, vd, new_vrs_key))
            );
            always_and_equality(
                lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, ov_set_nv.1, new_vrs_key, 0)),
                lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))
            );
            assert forall |s: ClusterState| {
                &&& conjuncted_current_state_matches_vrs(ov_set_nv.0)(s)
                &&& #[trigger] old_vrs_set_is_owned_by_vd(ov_set_nv.0, vd, new_vrs_key)(s)
                &&& current_state_matches_vrs_with_replicas_diff_and_key(vd, ov_set_nv.1, new_vrs_key, 0)(s)
                &&& inductive_current_state_matches(vd, controller_id, new_vrs_key)(s)
                &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
            } implies composed_current_state_matches(vd)(s) by {
                conjuncted_current_state_matches_old_vrs_0_implies_composed(vd, cluster, controller_id, ov_set_nv.0, ov_set_nv.1, new_vrs_key, s);
            }
            entails_preserved_by_always(
                lift_state(conjuncted_current_state_matches_vrs(ov_set_nv.0))
                    .and(lift_state(old_vrs_set_is_owned_by_vd(ov_set_nv.0, vd, new_vrs_key)))
                    .and(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, ov_set_nv.1, new_vrs_key, 0)))
                    .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
                    .and(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))),
                lift_state(composed_current_state_matches(vd))
            );
            always_and_equality_n!(
                lift_state(conjuncted_current_state_matches_vrs(ov_set_nv.0)),
                lift_state(old_vrs_set_is_owned_by_vd(ov_set_nv.0, vd, new_vrs_key)),
                lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, ov_set_nv.1, new_vrs_key, 0)),
                lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)),
                lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
            );
            entails_implies_leads_to(spec,
                always(lift_state(conjuncted_current_state_matches_vrs(ov_set_nv.0)))
                    .and(always(lift_state(old_vrs_set_is_owned_by_vd(ov_set_nv.0, vd, new_vrs_key))))
                    .and(always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, ov_set_nv.1, new_vrs_key, 0))))
                    .and(always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))))
                    .and(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
                always(lift_state(composed_current_state_matches(vd)))
            );
            always_double_equality(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)));
            leads_to_by_borrowing_inv(spec,
                always(lift_state(conjuncted_current_state_matches_vrs(ov_set_nv.0)))
                    .and(always(lift_state(old_vrs_set_is_owned_by_vd(ov_set_nv.0, vd, new_vrs_key))))
                    .and(always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, ov_set_nv.1, new_vrs_key, 0))))
                    .and(always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))),
                always(lift_state(composed_current_state_matches(vd))),
                always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))
            );
            always_and_equality(
                lift_state(conjuncted_current_state_matches_vrs(ov_set_nv.0)),
                lift_state(old_vrs_set_is_owned_by_vd(ov_set_nv.0, vd, new_vrs_key))
            );
            always_and_equality(
                lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, ov_set_nv.1, new_vrs_key, 0)),
                lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))
            );
            temp_pred_equality(
                all_vrs_post(ov_set_nv),
                always(lift_state(conjuncted_current_state_matches_vrs(ov_set_nv.0)))
                    .and(always(lift_state(old_vrs_set_is_owned_by_vd(ov_set_nv.0, vd, new_vrs_key))))
                    .and(always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, ov_set_nv.1, new_vrs_key, 0))))
                    .and(always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))))
            );
        }
        leads_to_exists_intro(spec, all_vrs_post, composed_vd_post);
        leads_to_trans(spec,
            p,
            tla_exists(all_vrs_post),
            composed_vd_post
        );
    }
    leads_to_exists_intro(spec,
        |new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))),
        always(lift_state(composed_current_state_matches(vd)))
    );
    leads_to_trans(spec,
        always(lift_state(desired_state_is(vd))),
        tla_exists(|new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))),
        always(lift_state(composed_current_state_matches(vd)))
    );
}

}
