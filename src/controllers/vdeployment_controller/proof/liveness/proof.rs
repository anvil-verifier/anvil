use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::*, message::*};
use crate::reconciler::spec::io::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_lemmas::*, liveness::{spec::*, terminate, resource_match::*, api_actions::*}, predicate::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*, util::*},
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*; // shortcut for steps
use crate::vdeployment_controller::proof::helper_invariants;
use crate::vreplicaset_controller::trusted::spec_types::*;
use vstd::{prelude::*, multiset::*};

verus! {

pub proof fn eventually_stable_reconciliation_holds_per_cr(spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        // The cluster always takes an action, and the relevant actions satisfy weak fairness.
        spec.entails(next_with_wf(cluster, controller_id)),
        // The vd type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        // The vrs type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        // The vd controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        // No other controllers interfere with the vd controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures
        spec.entails(vd_eventually_stable_reconciliation_per_cr(vd, controller_id)),
{
    // There are two specs we wish to deal with: one, `spec`, has `cluster.init()` true,
    // while the other spec, `stable_spec`, has it false.
    let stable_spec = stable_spec(cluster, controller_id);
    assumption_and_invariants_of_all_phases_is_stable(vd, cluster, controller_id);
    stable_spec_and_assumption_and_invariants_of_all_phases_is_stable(vd, cluster, controller_id);
    
    vd_rely_condition_equivalent_to_lifted_vd_rely_condition(
        stable_spec, cluster, controller_id
    );
    lemma_true_leads_to_always_current_state_matches(stable_spec, vd, cluster, controller_id);
    reveal_with_fuel(spec_before_phase_n, 7);

    spec_before_phase_n_entails_true_leads_to_current_state_matches(6, stable_spec, vd, cluster, controller_id);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(5, stable_spec, vd, cluster, controller_id);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(4, stable_spec, vd, cluster, controller_id);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(3, stable_spec, vd, cluster, controller_id);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(2, stable_spec, vd, cluster, controller_id);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(1, stable_spec, vd, cluster, controller_id);

    let assumption = always(lift_state(desired_state_is(vd)));
    temp_pred_equality(
        stable_spec.and(spec_before_phase_n(1, vd, cluster, controller_id)),
        stable_spec.and(invariants(vd, cluster, controller_id))
            .and(assumption)
    );
    unpack_conditions_from_spec(stable_spec.and(invariants(vd, cluster, controller_id)), assumption, true_pred(), always(lift_state(inductive_current_state_matches(vd, controller_id))));
    temp_pred_equality(true_pred().and(assumption), assumption);

    // Annoying non-automatic unpacking of the spec for one precondition.
    entails_trans(
        spec,
        next_with_wf(cluster, controller_id),
        always(lift_action(cluster.next()))
    );
    spec_entails_all_invariants(spec, vd, cluster, controller_id);
    simplify_predicate(spec, derived_invariants_since_beginning(vd, cluster, controller_id));

    spec_and_invariants_entails_stable_spec_and_invariants(spec, vd, cluster, controller_id);
    entails_trans(
        spec.and(derived_invariants_since_beginning(vd, cluster, controller_id)), 
        stable_spec.and(invariants(vd, cluster, controller_id)),
        always(lift_state(desired_state_is(vd))).leads_to(always(lift_state(inductive_current_state_matches(vd, controller_id))))
    );
}

proof fn spec_before_phase_n_entails_true_leads_to_current_state_matches(i: nat, spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int)
    requires
        1 <= i <= 6,
        valid(stable(spec.and(spec_before_phase_n(i, vd, cluster, controller_id)))),
        spec.and(spec_before_phase_n(i + 1, vd, cluster, controller_id)).entails(true_pred().leads_to(always(lift_state(inductive_current_state_matches(vd, controller_id))))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures spec.and(spec_before_phase_n(i, vd, cluster, controller_id)).entails(true_pred().leads_to(always(lift_state(inductive_current_state_matches(vd, controller_id))))),
{
    reveal_with_fuel(spec_before_phase_n, 7);
    temp_pred_equality(
        spec.and(spec_before_phase_n(i + 1, vd, cluster, controller_id)),
        spec.and(spec_before_phase_n(i, vd, cluster, controller_id))
            .and(invariants_since_phase_n(i, vd, cluster, controller_id))
    );
    spec_of_previous_phases_entails_eventually_new_invariants(spec, vd, cluster, controller_id, i);
    unpack_conditions_from_spec(spec.and(spec_before_phase_n(i, vd, cluster, controller_id)), invariants_since_phase_n(i, vd, cluster, controller_id), true_pred(), always(lift_state(inductive_current_state_matches(vd, controller_id))));
    temp_pred_equality(
        true_pred().and(invariants_since_phase_n(i, vd, cluster, controller_id)),
        invariants_since_phase_n(i, vd, cluster, controller_id)
    );
    leads_to_trans(spec.and(spec_before_phase_n(i, vd, cluster, controller_id)), true_pred(), invariants_since_phase_n(i, vd, cluster, controller_id), always(lift_state(inductive_current_state_matches(vd, controller_id))));
}

proof fn lemma_true_leads_to_always_current_state_matches(provided_spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int) 
    requires
        // The cluster always takes an action, and the relevant actions satisfy weak fairness.
        provided_spec.entails(next_with_wf(cluster, controller_id)),
        // The vd type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        // The vd controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        // No other controllers interfere with the vd controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> provided_spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures
        provided_spec.and(assumption_and_invariants_of_all_phases(vd, cluster, controller_id)).entails(true_pred().leads_to(always(lift_state(inductive_current_state_matches(vd, controller_id))))),
{
    let spec = provided_spec.and(assumption_and_invariants_of_all_phases(vd, cluster, controller_id));
    // non-interference properties
    vd_rely_condition_equivalent_to_lifted_vd_rely_condition(provided_spec, cluster, controller_id);
    entails_trans(spec, provided_spec, always(lifted_vd_rely_condition(cluster, controller_id)));
    only_interferes_with_itself_equivalent_to_lifted_only_interferes_with_itself_action(spec, cluster, controller_id);
    assert(spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))))) by {
        assert(spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref()))))) by {
            always_tla_forall_apply(spec, |vd: VDeploymentView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())), vd);
        }
        combine_spec_entails_always_n!(
            spec, lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
            lift_state(Cluster::crash_disabled(controller_id)),
            lift_state(Cluster::req_drop_disabled()),
            lift_state(Cluster::pod_monkey_disabled()),
            lift_state(Cluster::every_in_flight_msg_has_unique_id()),
            lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
            lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
            lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
            lift_state(Cluster::etcd_objects_have_unique_uids()),
            lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
            lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()),
            lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
            lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)),
            lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
            lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
            lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(controller_id)),
            lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
            lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
            lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)),
            lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)),
            lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VDeploymentView>(controller_id)),
            lift_state(Cluster::etcd_is_finite()),
            lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())),
            lift_state(Cluster::there_is_the_controller_state(controller_id)),
            lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)),
            lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)),
            lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()),
            lift_state(desired_state_is(vd)),
            lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vd.object_ref())),
            lift_state(helper_invariants::no_other_pending_request_interferes_with_vd_reconcile(vd, controller_id)),
            lift_state(helper_invariants::garbage_collector_does_not_delete_vd_vrs_objects(vd)),
            lift_state(helper_invariants::every_msg_from_vd_controller_carries_vd_key(controller_id)),
            lift_state(helper_invariants::vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)),
            lift_state(helper_invariants::vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id))
        );
    }
    // true ~> reconcile_idle
    let reconcile_idle = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
    };
    assert(spec.entails(true_pred().leads_to(lift_state(reconcile_idle)))) by {
        always_tla_forall_apply(spec, |vd: VDeploymentView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())), vd);
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
        always_to_always_later(spec, lift_state(desired_state_is(vd)));
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(desired_state_is(vd)),
            later(lift_state(desired_state_is(vd)))
        );
        cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(
            spec,
            controller_id,
            input,
            stronger_next,
            and!(stronger_reconcile_idle, desired_state_is(vd)),
            reconcile_scheduled
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
    // reconcile_scheduled ~> init
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
            spec,
            controller_id,
            input,
            stronger_next,
            ControllerStep::RunScheduledReconcile,
            reconcile_scheduled,
            init
        );
    }
    // init ~> done
    let done = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Done]),
        no_pending_req_in_cluster(vd, controller_id),
        current_state_matches(vd)
    );
    assert(spec.entails(lift_state(init).leads_to(lift_state(done)))) by {
        lemma_from_init_to_current_state_matches(vd, spec, cluster, controller_id);
    }
    let stable_final = inductive_current_state_matches(vd, controller_id);
    assert(lift_state(done).entails(lift_state(stable_final)));
    entails_implies_leads_to(spec, lift_state(done), lift_state(stable_final));
    // true ~> done
    leads_to_trans_n!(
        spec,
        true_pred(),
        lift_state(reconcile_idle),
        lift_state(reconcile_scheduled),
        lift_state(init),
        lift_state(done),
        lift_state(stable_final)
    );
    // true ~> []ESR
    assert(spec.entails(true_pred().leads_to(always(lift_state(stable_final))))) by {
        lemma_inductive_current_state_matches_is_stable(spec, vd, true_pred(), cluster, controller_id);
    }
}

#[verifier(rlimit(10))]
pub proof fn lemma_inductive_current_state_matches_is_stable(
    spec: TempPred<ClusterState>, vd: VDeploymentView, p: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    // spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))),
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    spec.entails(p.leads_to(lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Done]),
        no_pending_req_in_cluster(vd, controller_id),
        current_state_matches(vd)
    )))),
ensures
    spec.entails(p.leads_to(always(lift_state(inductive_current_state_matches(vd, controller_id))))),
{
    let inv = lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id));
    // ESR -> etcd_state_is (which is easier to reason about)
    let final_state = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Done]),
        no_pending_req_in_cluster(vd, controller_id),
        current_state_matches(vd)
    );
    entails_implies_leads_to(spec, lift_state(final_state), lift_state(inductive_current_state_matches(vd, controller_id)));
    leads_to_trans(spec, p, lift_state(final_state), lift_state(inductive_current_state_matches(vd, controller_id)));
    always_to_always_later(spec, lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime)
        &&& forall |vd: VDeploymentView| #[trigger] helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(cluster, controller_id)(s)
    };
    helper_invariants::lemma_spec_entails_lifted_cluster_invariants_since_reconciliation(spec, vd, cluster, controller_id);
    always_to_always_later(spec, lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)));
    vd_rely_condition_equivalent_to_lifted_vd_rely_condition(spec, cluster, controller_id);
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id),
        lifted_vd_rely_condition(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
        later(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))
    );
    assert forall |s, s_prime: ClusterState| inductive_current_state_matches(vd, controller_id)(s) && #[trigger] stronger_next(s, s_prime) implies inductive_current_state_matches(vd, controller_id)(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        lemma_inductive_current_state_matches_preserves_from_s_to_s_prime(s, s_prime, vd, cluster, controller_id, step);
    }
    leads_to_stable(spec, lift_action(stronger_next), p, lift_state(inductive_current_state_matches(vd, controller_id)));
    leads_to_always_enhance(spec, true_pred(), p, lift_state(inductive_current_state_matches(vd, controller_id)), lift_state(current_state_matches(vd)));
}

// similar to lemma_from_list_resp_to_next_state, carved out to reduce flakiness and proof time for debugging
pub proof fn lemma_inductive_current_state_matches_preserves_from_s_to_s_prime(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, step: Step
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime),
    Cluster::etcd_objects_have_unique_uids()(s),
    cluster.next_step(s, s_prime, step),
    forall |vd: VDeploymentView| #[trigger] helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s),
    vd_rely_condition(cluster, controller_id)(s),
    inductive_current_state_matches(vd, controller_id)(s),
ensures
    inductive_current_state_matches(vd, controller_id)(s_prime),
{
    VDeploymentView::marshal_preserves_integrity();
    VDeploymentReconcileState::marshal_preserves_integrity();
    assert(instantiated_etcd_state_is_with_zero_old_vrs(vd, controller_id)(s)) by {
        lemma_esr_equiv_to_instantiated_etcd_state_is(vd, cluster, controller_id, s);
    }
    let (uid, key) = choose |nv_uid_key: (Uid, ObjectRef)| {
        &&& #[trigger] etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, get_replicas(vd.spec.replicas))), 0)(s)
    };
    let new_msgs = s_prime.in_flight().sub(s.in_flight());
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            if s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()) {
                if msg.src != HostId::Controller(controller_id, vd.object_ref()) {
                    lemma_api_request_other_than_pending_req_msg_maintains_current_state_matches(
                        s, s_prime, vd, cluster, controller_id, msg
                    );
                    if at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s) {
                        assert(s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg is Some);
                        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                        assert(req_msg_is_list_vrs_req(vd, controller_id, req_msg, s));
                        assert forall |resp_msg| {
                            &&& #[trigger] s_prime.in_flight().contains(resp_msg)
                            &&& resp_msg.src is APIServer
                            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                        } implies resp_msg_is_ok_list_resp_containing_matched_vrs(vd, controller_id, resp_msg, s_prime) by {
                            assert(s.in_flight().contains(resp_msg)) by {
                                if !s.in_flight().contains(resp_msg) {
                                    assert(new_msgs.contains(resp_msg));
                                    assert(!resp_msg_matches_req_msg(resp_msg, req_msg));
                                }
                            }
                            lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
                                s, s_prime, vd, cluster, controller_id, msg, Some(uid)
                            );
                            let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                            let vrs_list = objects_to_vrs_list(resp_objs)->0;
                            let managed_vrs_list = vrs_list.filter(|vrs| valid_owned_vrs(vrs, vd));
                            assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies {
                                let key = vrs.object_ref();
                                let etcd_vrs = VReplicaSetView::unmarshal(s_prime.resources()[key])->Ok_0;
                                &&& s_prime.resources().contains_key(key)
                                &&& VReplicaSetView::unmarshal(s_prime.resources()[key]) is Ok
                                &&& valid_owned_obj_key(vd, s_prime)(key)
                                &&& vrs_weakly_eq(etcd_vrs, vrs)
                                &&& etcd_vrs.spec == vrs.spec
                            } by {
                                let key = vrs.object_ref();
                                let etcd_obj = s.resources()[key];
                                let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
                                assert(etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]) by {
                                    assert(vrs_weakly_eq(etcd_vrs, vrs));
                                    VReplicaSetView::marshal_preserves_integrity();
                                }
                                lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
                                    s, s_prime, vd, cluster, controller_id, msg
                                );
                            }
                        }
                        assert(at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s_prime));
                        assert(current_state_matches(vd)(s_prime));
                        assert(inductive_current_state_matches(vd, controller_id)(s_prime)); // sentry for debugging
                    }
                } else {
                    assert(s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()));
                    let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                    assert(input == Some(req_msg));
                    if at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s) {
                        let req_msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                        assert forall |msg| {
                            &&& #[trigger] s_prime.in_flight().contains(msg)
                            &&& msg.src is APIServer
                            &&& resp_msg_matches_req_msg(msg, req_msg)
                        } implies resp_msg_is_ok_list_resp_containing_matched_vrs(vd, controller_id, msg, s) by {
                            if !new_msgs.contains(msg) {
                                assert(s.in_flight().contains(msg));
                            } else {
                                lemma_list_vrs_request_returns_ok_with_objs_matching_vd(
                                    s, s_prime, vd, cluster, controller_id, req_msg,
                                );
                            }
                        }
                        assert(inductive_current_state_matches(vd, controller_id)(s_prime));
                    }
                    assert(inductive_current_state_matches(vd, controller_id)(s_prime));
                }
                assert(inductive_current_state_matches(vd, controller_id)(s_prime));
            } else {
                assert(msg.src != HostId::Controller(controller_id, vd.object_ref()));
                lemma_api_request_other_than_pending_req_msg_maintains_current_state_matches(
                    s, s_prime, vd, cluster, controller_id, msg
                );
                assert(inductive_current_state_matches(vd, controller_id)(s_prime));
            }
            assert(inductive_current_state_matches(vd, controller_id)(s_prime));
        },
        Step::ControllerStep(input) => {
            if s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
                && input.0 == controller_id && input.2 == Some(vd.object_ref()) {
                let resp_msg = input.1->0;
                if at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s) {
                    // similar to proof in lemma_from_init_to_current_state_matches, yet replicas and old_vrs_list_len are fixed
                    assert(exists |nv_uid_key: (Uid, ObjectRef)| #[trigger] new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(vd, controller_id, resp_msg, Some((nv_uid_key.0, nv_uid_key.1, get_replicas(vd.spec.replicas))), 0)(s)) by {
                        lemma_etcd_state_is_implies_filter_old_and_new_vrs_from_resp_objs(
                            vd, cluster, controller_id, (uid, key), resp_msg, s
                        );
                    }
                    let nv_uid_key = choose |nv_uid_key: (Uid, ObjectRef)| {
                        &&& #[trigger] new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(vd, controller_id, resp_msg, Some((nv_uid_key.0, nv_uid_key.1, get_replicas(vd.spec.replicas))), 0)(s)
                    };
                    lemma_from_list_resp_to_next_state(
                        s, s_prime, vd, cluster, controller_id, resp_msg, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(1))), 0
                    );
                    assert(at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS])(s_prime));
                    let vds_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
                    assert(vds_prime.old_vrs_index == 0);
                    assert(inductive_current_state_matches(vd, controller_id)(s_prime));
                } else if at_vd_step_with_vd(vd, controller_id, at_step![Init])(s) {
                    // prove that the newly sent message has no response.
                    if s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg is Some {
                        let req_msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                        assert(forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id);
                        assert(s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg));
                        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg)
                            && (forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id)
                            && s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg)
                            && msg != req_msg
                            implies msg.rpc_id != req_msg.rpc_id by {
                            if !s.in_flight().contains(msg) {} // need this to invoke trigger.
                        }
                    }
                } else if at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS])(s) {
                    // it directly goes to Done
                }
                assert(inductive_current_state_matches(vd, controller_id)(s_prime));
            } else if !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()) {
                if s_prime.ongoing_reconciles(controller_id).contains_key(vd.object_ref()) { // RunScheduledReconcile
                    assert(s_prime.resources() == s.resources());
                    assert(at_vd_step_with_vd(vd, controller_id, at_step![Init])(s_prime)) by {
                        assert(helper_invariants::vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)(s_prime));
                        lemma_cr_fields_eq_to_cr_predicates_eq(vd, controller_id, s_prime);
                    }
                    assert(inductive_current_state_matches(vd, controller_id)(s_prime));
                } else {
                    assert(s_prime.resources() == s.resources());
                    assert(inductive_current_state_matches(vd, controller_id)(s_prime));
                }
                assert(inductive_current_state_matches(vd, controller_id)(s_prime));
            } else { // same controller_id, different CR
                assert(s.ongoing_reconciles(controller_id)[vd.object_ref()] == s_prime.ongoing_reconciles(controller_id)[vd.object_ref()]);
                assert(s.resources() == s_prime.resources());
                if at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s) {
                    let req_msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                    assert forall |msg| {
                        &&& #[trigger] s_prime.in_flight().contains(msg)
                        &&& msg.src is APIServer
                        &&& resp_msg_matches_req_msg(msg, req_msg)
                    } implies resp_msg_is_ok_list_resp_containing_matched_vrs(vd, controller_id, msg, s) by {
                        if !new_msgs.contains(msg) {
                            assert(s.in_flight().contains(msg));
                        }
                    }
                }
                assert(inductive_current_state_matches(vd, controller_id)(s_prime));
            }
            assert(inductive_current_state_matches(vd, controller_id)(s_prime));
        },
        _ => { // this branch is slow
            // Maintain quantified invariant.
            if at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s) {
                let req_msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                assert forall |msg| {
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.src is APIServer
                    &&& resp_msg_matches_req_msg(msg, req_msg)
                } implies resp_msg_is_ok_list_resp_containing_matched_vrs(vd, controller_id, msg, s) by {
                    if !new_msgs.contains(msg) {
                        assert(s.in_flight().contains(msg));
                    }
                }
                assert(inductive_current_state_matches(vd, controller_id)(s_prime));
            }
            assert(inductive_current_state_matches(vd, controller_id)(s_prime));
        }
    }
}

}
