use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::*, message::*};
use crate::reconciler::spec::io::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_lemmas::*, liveness::{spec::*, terminate, resource_match::*, api_actions::*, rolling_update::composition::*}, predicate::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*; // shortcut for steps
use crate::vdeployment_controller::proof::helper_invariants;
use crate::vreplicaset_controller::trusted::{spec_types::*, liveness_theorem as vrs_liveness};
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
    unpack_conditions_from_spec(stable_spec.and(invariants(vd, cluster, controller_id)), assumption, true_pred(), tla_exists(|new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))));
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
        always(lift_state(desired_state_is(vd))).leads_to(tla_exists(|new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))))
    );
}

proof fn spec_before_phase_n_entails_true_leads_to_current_state_matches(i: nat, spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int)
    requires
        1 <= i <= 6,
        valid(stable(spec.and(spec_before_phase_n(i, vd, cluster, controller_id)))),
        spec.and(spec_before_phase_n(i + 1, vd, cluster, controller_id)).entails(true_pred().leads_to(tla_exists(|new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures spec.and(spec_before_phase_n(i, vd, cluster, controller_id)).entails(true_pred().leads_to(tla_exists(|new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))))),
{
    reveal_with_fuel(spec_before_phase_n, 7);
    temp_pred_equality(
        spec.and(spec_before_phase_n(i + 1, vd, cluster, controller_id)),
        spec.and(spec_before_phase_n(i, vd, cluster, controller_id))
            .and(invariants_since_phase_n(i, vd, cluster, controller_id))
    );
    spec_of_previous_phases_entails_eventually_new_invariants(spec, vd, cluster, controller_id, i);
    unpack_conditions_from_spec(spec.and(spec_before_phase_n(i, vd, cluster, controller_id)), invariants_since_phase_n(i, vd, cluster, controller_id), true_pred(), tla_exists(|new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))));
    temp_pred_equality(
        true_pred().and(invariants_since_phase_n(i, vd, cluster, controller_id)),
        invariants_since_phase_n(i, vd, cluster, controller_id)
    );
    leads_to_trans(spec.and(spec_before_phase_n(i, vd, cluster, controller_id)), true_pred(), invariants_since_phase_n(i, vd, cluster, controller_id), tla_exists(|new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))));
}

pub proof fn spec_entails_assumptions_and_invariants_of_all_phases_implies_cluster_invariants_since_reconciliation(
    spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(assumption_and_invariants_of_all_phases(vd, cluster, controller_id)),
ensures
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
{
    assert(assumption_and_invariants_of_all_phases(vd, cluster, controller_id).entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref()))))) by {
        always_tla_forall_apply(assumption_and_invariants_of_all_phases(vd, cluster, controller_id), |vd: VDeploymentView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())), vd);
    }
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::crash_disabled(controller_id))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::req_drop_disabled())));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::pod_monkey_disabled())));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::every_in_flight_msg_has_unique_id())));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::etcd_objects_have_unique_uids())));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>())));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>())));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(controller_id))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VDeploymentView>(controller_id))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::etcd_is_finite())));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref()))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::there_is_the_controller_state(controller_id))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers())));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(desired_state_is(vd))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vd.object_ref()))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vd_reconcile(vd, controller_id))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(helper_invariants::garbage_collector_does_not_delete_vd_vrs_objects(vd))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(helper_invariants::every_msg_from_vd_controller_carries_vd_key(controller_id))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(helper_invariants::vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id))));
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_state(helper_invariants::vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id))));
    combine_spec_entails_always_n!(spec,
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
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
        provided_spec.and(assumption_and_invariants_of_all_phases(vd, cluster, controller_id)).entails(true_pred().leads_to(tla_exists(|new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))))),
{
    let spec = provided_spec.and(assumption_and_invariants_of_all_phases(vd, cluster, controller_id));
    // non-interference properties
    vd_rely_condition_equivalent_to_lifted_vd_rely_condition(provided_spec, cluster, controller_id);
    entails_trans(spec, provided_spec, always(lifted_vd_rely_condition(cluster, controller_id)));
    only_interferes_with_itself_equivalent_to_lifted_only_interferes_with_itself_action(spec, cluster, controller_id);
    only_interferes_with_itself_equivalent_to_lifted_only_interferes_with_itself(spec, cluster, controller_id);
    spec_entails_assumptions_and_invariants_of_all_phases_implies_cluster_invariants_since_reconciliation(spec, vd, cluster, controller_id);
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
    assert(spec.entails(lift_state(done).leads_to(tla_exists(|new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))))))) by {
        let k_to_csm = |new_vrs_key: ObjectRef| inductive_current_state_matches(vd, controller_id, new_vrs_key);
        let lifted_k_to_csm = |new_vrs_key: ObjectRef| lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key));
        tla_exists_p_tla_exists_q_equality(
            |new_vrs_key: ObjectRef| lift_state(k_to_csm(new_vrs_key)),
            lifted_k_to_csm
        );
        temp_pred_equality(
            tla_exists(|new_vrs_key: ObjectRef| lift_state(k_to_csm(new_vrs_key))),
            tla_exists(lifted_k_to_csm)
        );
        assert forall |ex| #[trigger] lift_state(done).satisfied_by(ex) implies exists |k| #[trigger] lifted_k_to_csm(k).satisfied_by(ex) by {
            let s = ex.head();
            let nv_key = choose |new_vrs_key: ObjectRef| {
                let etcd_obj = s.resources()[new_vrs_key];
                let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
                &&& #[trigger] s.resources().contains_key(new_vrs_key)
                &&& valid_owned_obj_key(vd, s)(new_vrs_key)
                &&& filter_new_vrs_keys(vd.spec.template, s)(new_vrs_key)
                &&& etcd_vrs.metadata.uid is Some
                &&& vd.spec.replicas.unwrap_or(1) > 0 ==> etcd_vrs.spec.replicas.unwrap_or(1) > 0
                // no old vrs, including the 2nd new vrs (if any)
                &&& !exists |old_k: ObjectRef| {
                    &&& #[trigger] s.resources().contains_key(old_k)
                    &&& valid_owned_obj_key(vd, s)(old_k)
                    &&& filter_old_vrs_keys(Some(etcd_vrs.metadata.uid->0), s)(old_k)
                }
            };
            assert(current_state_matches_with_new_vrs_key(vd, nv_key)(s));
            assert(lifted_k_to_csm(nv_key).satisfied_by(ex));
        }
        entails_implies_leads_to(spec, lift_state(done), tla_exists(lifted_k_to_csm));
        let stronger_next = |s, s_prime| {
            &&& cluster.next()(s, s_prime)
            &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
            &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime)
            &&& vd_reconcile_request_only_interferes_with_itself_condition(controller_id)(s)
            &&& vd_rely_condition(cluster, controller_id)(s)
        };
        temp_pred_equality(
            lift_state(vd_rely_condition(cluster, controller_id)),
            lifted_vd_rely_condition(cluster, controller_id)
        );
        always_to_always_later(spec, lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)));
        combine_spec_entails_always_n!(spec,
            lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
            later(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))),
            lift_state(vd_reconcile_request_only_interferes_with_itself_condition(controller_id)),
            lift_state(vd_rely_condition(cluster, controller_id))
        );
        assert forall |s, s_prime| (forall |nv_key: ObjectRef| #[trigger] k_to_csm(nv_key)(s) && #[trigger] stronger_next(s, s_prime) ==> k_to_csm(nv_key)(s_prime)) by {
            assert forall |nv_key: ObjectRef| #[trigger] k_to_csm(nv_key)(s) && stronger_next(s, s_prime) implies k_to_csm(nv_key)(s_prime) by {
                lemma_inductive_current_state_matches_preserves_from_s_to_s_prime_with_nv_key(vd, controller_id, cluster, nv_key, s, s_prime);
            }
        }
        leads_to_exists_stable(spec, stronger_next, lift_state(done), k_to_csm);
        tla_exists_p_tla_exists_q_equality(
            |new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))),
            |new_vrs_key: ObjectRef| always(lift_state(k_to_csm(new_vrs_key)))
        );
    }
    leads_to_trans_n!(spec,
        true_pred(),
        lift_state(reconcile_idle),
        lift_state(reconcile_scheduled),
        lift_state(init),
        lift_state(done),
        tla_exists(|new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))))
    );
}

// Wrapper: takes per-id rely conditions (matching composition trait interface),
// derives always(lifted_vd_rely_condition) and always(lifted_vd_reconcile_request_only_interferes_with_itself) internally,
// calls the per-CR proof and rolling update composition,
// and universally quantifies over vd to produce the full composed ESR.
pub proof fn lemma_vd_composed_eventually_stable_reconciliation(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(next_with_wf(cluster, controller_id)),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(vrs_liveness::vrs_eventually_stable_reconciliation()),
    ensures
        spec.entails(composed_vd_eventually_stable_reconciliation()),
{
    // Derive always(lifted_vd_rely_condition)
    vd_rely_condition_equivalent_to_lifted_vd_rely_condition(spec, cluster, controller_id);

    // Extract always(lift_action(cluster.next())) from next_with_wf
    entails_trans(spec, next_with_wf(cluster, controller_id), always(lift_action(cluster.next())));

    // Derive always(lifted_vd_reconcile_request_only_interferes_with_itself)
    assert(spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)))) by {
        assert forall |vd| #[trigger] spec.entails(always(lift_state(helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)))) by {
            helper_invariants::lemma_always_vd_reconcile_request_only_interferes_with_itself(spec, cluster, controller_id, vd);
        }
        spec_entails_tla_forall(spec, |vd| always(lift_state(helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd))));
        spec_entails_always_tla_forall_equality(spec, |vd| lift_state(helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)));
        only_interferes_with_itself_equivalent_to_lifted_only_interferes_with_itself(spec, cluster, controller_id);
    }

    assert forall |vd: VDeploymentView| #[trigger] spec.entails(
        always(lift_state(desired_state_is(vd))).leads_to(
            always(lift_state(composed_current_state_matches(vd))))
    ) by {
        // Per-CR ESR proof
        eventually_stable_reconciliation_holds_per_cr(spec, vd, cluster, controller_id);
        // Composition with VRS ESR via rolling update
        spec_entails_always_cluster_invariants_since_reconciliation_holds_pre_cr(spec, vd, controller_id, cluster);
        spec_entails_always_desired_state_is_leads_to_assumption_and_invariants_of_all_phases(spec, vd, cluster, controller_id);
        rolling_update_leads_to_composed_current_state_matches_vd(spec, vd, controller_id, cluster);
    }
    spec_entails_tla_forall(spec, |vd: VDeploymentView|
        always(lift_state(desired_state_is(vd))).leads_to(
            always(lift_state(composed_current_state_matches(vd)))));
    tla_forall_p_tla_forall_q_equality(
        |vd: VDeploymentView| composed_vd_eventually_stable_reconciliation_per_cr()(vd),
        |vd: VDeploymentView| always(lift_state(desired_state_is(vd))).leads_to(always(lift_state(composed_current_state_matches(vd))))
    );
}

}
