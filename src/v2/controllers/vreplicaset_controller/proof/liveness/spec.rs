#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::{
    spec::{
        api_server::{state_machine::*, types::*},
        cluster::*,
        controller::types::*,
        message::*,
        esr::*,
    },
    proof::{controller_runtime_liveness::*, network::*},
};

use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
    proof::{helper_invariants::{predicate::*, proof::*}, liveness::*, predicate::*},
};
use crate::reconciler::spec::io::*;
use vstd::{map::*, map_lib::*, math::*, prelude::*};

verus! {

pub open spec fn assumption_and_invariants_of_all_phases(vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    invariants(vrs, cluster, controller_id)
    .and(always(lift_state(Cluster::desired_state_is(vrs))))
    .and(invariants_since_phase_i(controller_id, vrs))
    .and(invariants_since_phase_ii(controller_id, vrs))
    .and(invariants_since_phase_iii(vrs, cluster, controller_id))
    .and(invariants_since_phase_iv(vrs, cluster, controller_id))
    .and(invariants_since_phase_v(vrs, cluster, controller_id))
    .and(invariants_since_phase_vi(vrs, cluster, controller_id))
    .and(invariants_since_phase_vii(vrs, cluster, controller_id))
}

pub proof fn assumption_and_invariants_of_all_phases_is_stable(vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    ensures
        valid(stable(assumption_and_invariants_of_all_phases(vrs, cluster, controller_id))),
        valid(stable(invariants(vrs, cluster, controller_id))),
        forall |i: nat| 0 <= i <= 7 ==> valid(stable(#[trigger] spec_before_phase_n(i, vrs, cluster, controller_id))),
{
    reveal_with_fuel(spec_before_phase_n, 7);
    invariants_is_stable(vrs, cluster, controller_id);
    always_p_is_stable(lift_state(Cluster::desired_state_is(vrs)));
    invariants_since_phase_i_is_stable(controller_id, vrs);
    invariants_since_phase_ii_is_stable(controller_id, vrs);
    invariants_since_phase_iii_is_stable(vrs, cluster, controller_id);
    invariants_since_phase_iv_is_stable(vrs, cluster, controller_id);
    invariants_since_phase_v_is_stable(vrs, cluster, controller_id);
    invariants_since_phase_vi_is_stable(vrs, cluster, controller_id);
    invariants_since_phase_vii_is_stable(vrs, cluster, controller_id);
    stable_and_n!(
        invariants(vrs, cluster, controller_id),
        always(lift_state(Cluster::desired_state_is(vrs))),
        invariants_since_phase_i(controller_id, vrs),
        invariants_since_phase_ii(controller_id, vrs),
        invariants_since_phase_iii(vrs, cluster, controller_id),
        invariants_since_phase_iv(vrs, cluster, controller_id),
        invariants_since_phase_v(vrs, cluster, controller_id),
        invariants_since_phase_vi(vrs, cluster, controller_id),
        invariants_since_phase_vii(vrs, cluster, controller_id)
    );
}

pub open spec fn invariants_since_phase_n(n: nat, vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    if n == 0 {
        invariants(vrs, cluster, controller_id)
        .and(always(lift_state(Cluster::desired_state_is(vrs))))
    } else if n == 1 {
        invariants_since_phase_i(controller_id, vrs)
    } else if n == 2 {
        invariants_since_phase_ii(controller_id, vrs)
    } else if n == 3 {
        invariants_since_phase_iii(vrs, cluster, controller_id)
    } else if n == 4 {
        invariants_since_phase_iv(vrs, cluster, controller_id)
    } else if n == 5 {
        invariants_since_phase_v(vrs, cluster, controller_id)
    } else if n == 6 {
        invariants_since_phase_vi(vrs, cluster, controller_id)
    } else if n == 7 {
        invariants_since_phase_vii(vrs, cluster, controller_id)
    } else {
        true_pred()
    }
}

pub open spec fn spec_before_phase_n(n: nat, vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
    decreases n,
{
    if n == 1 {
        invariants(vrs, cluster, controller_id).and(always(lift_state(Cluster::desired_state_is(vrs))))
    } else if 2 <= n <= 8 {
        spec_before_phase_n((n-1) as nat, vrs, cluster, controller_id).and(invariants_since_phase_n((n-1) as nat, vrs, cluster, controller_id))
    } else {
        true_pred()
    }
}

pub open spec fn invariants_since_phase_i(controller_id: int, vrs: VReplicaSetView) -> TempPred<ClusterState> {
    always(lift_state(Cluster::crash_disabled(controller_id)))
    .and(always(lift_state(Cluster::req_drop_disabled())))
    .and(always(lift_state(Cluster::pod_monkey_disabled())))
    .and(always(lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, vrs))))
}

pub proof fn invariants_since_phase_i_is_stable(controller_id: int, vrs: VReplicaSetView)
    ensures valid(stable(invariants_since_phase_i(controller_id, vrs))),
{
    stable_and_always_n!(
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, vrs))
    );
}

pub open spec fn invariants_since_phase_ii(controller_id: int, vrs: VReplicaSetView) -> TempPred<ClusterState>
{
    always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs)))
}

pub proof fn invariants_since_phase_ii_is_stable(controller_id: int, vrs: VReplicaSetView)
    ensures valid(stable(invariants_since_phase_ii(controller_id, vrs))),
{
    always_p_is_stable(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs)));
}

pub open spec fn invariants_since_phase_iii(vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(no_pending_update_or_update_status_request_on_pods()))
    .and(always(lift_state(no_pending_create_or_delete_request_not_from_controller_on_pods())))
    .and(always(lift_state(every_create_request_is_well_formed(cluster, controller_id))))
}

pub proof fn invariants_since_phase_iii_is_stable(vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants_since_phase_iii(vrs, cluster, controller_id))),
{
    stable_and_always_n!(
        lift_state(no_pending_update_or_update_status_request_on_pods()),
        lift_state(no_pending_create_or_delete_request_not_from_controller_on_pods()),
        lift_state(every_create_request_is_well_formed(cluster, controller_id))
    );
}

pub open spec fn invariants_since_phase_iv(vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id)))
}

pub proof fn invariants_since_phase_iv_is_stable(vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants_since_phase_iv(vrs, cluster, controller_id))),
{
    always_p_is_stable(
        lift_state(each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id))
    );
}

pub open spec fn invariants_since_phase_v(vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))
}

pub proof fn invariants_since_phase_v_is_stable(vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants_since_phase_v(vrs, cluster, controller_id))),
{
    always_p_is_stable(
        lift_state(every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id))
    );
}

pub open spec fn invariants_since_phase_vi(vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(garbage_collector_does_not_delete_vrs_pods(vrs)))
    .and(always(lift_state(every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id))))
    .and(always(lift_state(every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id))))
}

pub proof fn invariants_since_phase_vi_is_stable(vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants_since_phase_vi(vrs, cluster, controller_id))),
{
    stable_and_always_n!(
        lift_state(garbage_collector_does_not_delete_vrs_pods(vrs)),
        lift_state(every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)),
        lift_state(every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id))
    );
}

pub open spec fn invariants_since_phase_vii(vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(vrs, controller_id)))
}

pub proof fn invariants_since_phase_vii_is_stable(vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants_since_phase_vii(vrs, cluster, controller_id))),
{
    always_p_is_stable(lift_state(at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(vrs, controller_id)));
}

pub proof fn spec_of_previous_phases_entails_eventually_new_invariants(provided_spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int, i: nat)
    requires 
        1 <= i <= 7,
        // The vrs type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        // The vrs controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        // No other controllers interfere with the vrs controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> provided_spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(controller_id, other_id)))),
    ensures provided_spec.and(spec_before_phase_n(i, vrs, cluster, controller_id)).entails(true_pred().leads_to(invariants_since_phase_n(i, vrs, cluster, controller_id))),
{
    let spec = provided_spec.and(spec_before_phase_n(i, vrs, cluster, controller_id));
    // assert non-interference property on combined spec.
    assert forall |other_id| 
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id) 
            ==> provided_spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(controller_id, other_id)))))
        implies 
        cluster.controller_models.remove(controller_id).contains_key(other_id) 
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(controller_id, other_id)))) by {
        if cluster.controller_models.remove(controller_id).contains_key(other_id) {
            assert(provided_spec.entails(always(lift_state(vrs_not_interfered_by(controller_id, other_id)))));
            entails_and_different_temp(
                provided_spec,
                spec_before_phase_n(i, vrs, cluster, controller_id),
                always(lift_state(vrs_not_interfered_by(controller_id, other_id))),
                true_pred()
            );
            assert(spec.entails(always(lift_state(vrs_not_interfered_by(controller_id, other_id))).and(true_pred())));
            temp_pred_equality(
                always(lift_state(vrs_not_interfered_by(controller_id, other_id))).and(true_pred()),
                always(lift_state(vrs_not_interfered_by(controller_id, other_id)))
            );
        }
    }

    reveal_with_fuel(spec_before_phase_n, 7);
    if i == 1 {
        use_tla_forall(spec, |input| cluster.disable_crash().weak_fairness(input), controller_id);
        cluster.lemma_true_leads_to_crash_always_disabled(spec, controller_id);
        cluster.lemma_true_leads_to_req_drop_always_disabled(spec);
        cluster.lemma_true_leads_to_pod_monkey_always_disabled(spec);
        cluster.lemma_true_leads_to_always_the_object_in_schedule_has_spec_and_uid_as(spec, controller_id, vrs);
        leads_to_always_combine_n!(
            spec,
            true_pred(),
            lift_state(Cluster::crash_disabled(controller_id)),
            lift_state(Cluster::req_drop_disabled()),
            lift_state(Cluster::pod_monkey_disabled()),
            lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, vrs))
        );
    } else {
        terminate::reconcile_eventually_terminates(spec, cluster, controller_id);
        // PROVE THEIR EQUIVALENCE
        // assume(
        //     spec.entails(tla_forall(|key| 
        //         true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key)))
        //     ))
        // );
        use_tla_forall(
            spec,
            |vrs: VReplicaSetView| 
                true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()))),
            vrs
        );
        if i == 2 {
            cluster.lemma_true_leads_to_always_the_object_in_reconcile_has_spec_and_uid_as(spec, controller_id, vrs);
        } else if i == 3 {
            lemma_eventually_always_no_pending_update_or_update_status_request_on_pods(spec, cluster, controller_id);
            lemma_eventually_always_no_pending_create_or_delete_request_not_from_controller_on_pods(spec, cluster, controller_id);
            lemma_eventually_always_every_create_request_is_well_formed(spec, cluster, controller_id);
            leads_to_always_combine_n!(
                spec,
                true_pred(),
                lift_state(no_pending_update_or_update_status_request_on_pods()),
                lift_state(no_pending_create_or_delete_request_not_from_controller_on_pods()),
                lift_state(every_create_request_is_well_formed(cluster, controller_id))
            );
        } else if i == 4 {
            lemma_eventually_always_each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(spec, vrs, cluster, controller_id);
        } else if i == 5 {
            always_tla_forall_apply(spec, |vrs: VReplicaSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())), vrs);
            lemma_eventually_always_every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(spec, vrs, cluster, controller_id);
        } else if i == 6 {
            always_tla_forall_apply(spec, |vrs: VReplicaSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())), vrs);
            lemma_eventually_always_garbage_collector_does_not_delete_vrs_pods(spec, vrs, cluster, controller_id);
            lemma_eventually_always_every_create_matching_pod_request_implies_at_after_create_pod_step(spec, vrs, cluster, controller_id);
            lemma_eventually_always_every_delete_matching_pod_request_implies_at_after_delete_pod_step(spec, vrs, cluster, controller_id);
            leads_to_always_combine_n!(
                spec, 
                true_pred(),
                lift_state(garbage_collector_does_not_delete_vrs_pods(vrs)),
                lift_state(every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)),
                lift_state(every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id))
            );
        } else if i == 7 {
            lemma_eventually_always_at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(spec, vrs, cluster, controller_id);
        }
    }
}

pub open spec fn stable_spec(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    next_with_wf(cluster, controller_id)
    .and(always(lifted_vrs_non_interference_property(cluster, controller_id)))
}

pub proof fn stable_spec_is_stable(cluster: Cluster, controller_id: int)
    ensures valid(stable(stable_spec(cluster, controller_id))),
{
    next_with_wf_is_stable(cluster, controller_id);
    always_p_is_stable(lifted_vrs_non_interference_property(cluster, controller_id));
    stable_and_n!(
        next_with_wf(cluster, controller_id),
        always(lifted_vrs_non_interference_property(cluster, controller_id))
    );
}

pub open spec fn next_with_wf(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    always(lift_action(cluster.next()))
    .and(tla_forall(|input| cluster.api_server_next().weak_fairness(input)))
    .and(tla_forall(|input| cluster.builtin_controllers_next().weak_fairness(input)))
    .and(tla_forall(|input: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, input.0, input.1))))
    .and(tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness((controller_id, input))))
    .and(tla_forall(|input| cluster.disable_crash().weak_fairness(input)))
    .and(tla_forall(|input| cluster.external_next().weak_fairness((controller_id, input))))
    .and(cluster.disable_req_drop().weak_fairness(()))
    .and(cluster.disable_pod_monkey().weak_fairness(()))
}

pub proof fn next_with_wf_is_stable(cluster: Cluster, controller_id: int)
    ensures valid(stable(next_with_wf(cluster, controller_id))),
{
    always_p_is_stable(lift_action(cluster.next()));
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.api_server_next());
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.builtin_controllers_next());
    cluster.tla_forall_controller_next_weak_fairness_is_stable(controller_id);
    cluster.tla_forall_schedule_controller_reconcile_weak_fairness_is_stable(controller_id);
    cluster.tla_forall_external_next_weak_fairness_is_stable(controller_id);
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.disable_crash());
    Cluster::action_weak_fairness_is_stable(cluster.disable_req_drop());
    Cluster::action_weak_fairness_is_stable(cluster.disable_pod_monkey());
    stable_and_n!(
        always(lift_action(cluster.next())),
        tla_forall(|input| cluster.api_server_next().weak_fairness(input)),
        tla_forall(|input| cluster.builtin_controllers_next().weak_fairness(input)),
        tla_forall(|input: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, input.0, input.1))),
        tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness((controller_id, input))),
        tla_forall(|input| cluster.disable_crash().weak_fairness(input)),
        tla_forall(|input| cluster.external_next().weak_fairness((controller_id, input))),
        cluster.disable_req_drop().weak_fairness(()),
        cluster.disable_pod_monkey().weak_fairness(())
    );
}

// This predicate combines all the possible actions (next), weak fairness and invariants that hold throughout the execution.
// We name it invariants here because these predicates are never violated, thus they can all be seen as some kind of invariants.
//
// The final goal of our proof is to show init /\ invariants |= []desired_state_is(vrs) ~> []current_state_matches(vrs).
// init /\ invariants is equivalent to init /\ next /\ weak_fairness, so we get cluster_spec() |= []desired_state_is(vrs) ~> []current_state_matches(vrs).
pub open spec fn invariants(vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    next_with_wf(cluster, controller_id).and(derived_invariants_since_beginning(vrs, cluster, controller_id))
}

pub proof fn invariants_is_stable(vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants(vrs, cluster, controller_id))),
{
    next_with_wf_is_stable(cluster, controller_id);
    derived_invariants_since_beginning_is_stable(vrs, cluster, controller_id);
    stable_and_n!(
        next_with_wf(cluster, controller_id),
        derived_invariants_since_beginning(vrs, cluster, controller_id)
    );
}

pub open spec fn derived_invariants_since_beginning(vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())))
    .and(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())))
    .and(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>())))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id))))
    .and(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())))
    .and(always(lift_state(vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id))))
    .and(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())))
    .and(always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id))))
    .and(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))))
    .and(always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id))))
    .and(always(lift_state(Cluster::etcd_is_finite())))
    .and(always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))))
    .and(always(lift_state(Cluster::there_is_the_controller_state(controller_id))))
    .and(always(lift_state(Cluster::there_is_no_request_msg_to_external(controller_id))))
    .and(always(lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id))))
    .and(always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::Init))))))
    .and(always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::AfterListPods))))))
    .and(always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), unwrap_local_state_closure(
        |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()
    ))))))
    .and(always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), unwrap_local_state_closure(
        |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
    ))))))
}

pub proof fn derived_invariants_since_beginning_is_stable(vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(derived_invariants_since_beginning(vrs, cluster, controller_id))),
{
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_has_unique_id()));
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()));
    always_p_is_stable(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)));
    always_p_is_stable(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()));
    always_p_is_stable(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()));
    always_p_is_stable(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()));
    always_p_is_stable(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)));
    always_p_is_stable(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()));
    always_p_is_stable(lift_state(vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)));
    always_p_is_stable(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()));
    always_p_is_stable(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id)));
    always_p_is_stable(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)));
    always_p_is_stable(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)));
    always_p_is_stable(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)));
    always_p_is_stable(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)));
    always_p_is_stable(lift_state(Cluster::etcd_is_finite()));
    always_p_is_stable(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref()))));
    always_p_is_stable(lift_state(Cluster::there_is_the_controller_state(controller_id)));
    always_p_is_stable(lift_state(Cluster::there_is_no_request_msg_to_external(controller_id)));
    always_p_is_stable(lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)));
    always_p_is_stable(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::Init)))));
    always_p_is_stable(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::AfterListPods)))));
    always_p_is_stable(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), unwrap_local_state_closure(
        |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()
    )))));
    always_p_is_stable(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), unwrap_local_state_closure(
        |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
    )))));

    stable_and_n!(
        always(lift_state(Cluster::every_in_flight_msg_has_unique_id())),
        always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())),
        always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))),
        always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())),
        always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())),
        always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>())),
        always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id))),
        always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())),
        always(lift_state(vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id))),
        always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())),
        always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id))),
        always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))),
        always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))),
        always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))),
        always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id))),
        always(lift_state(Cluster::etcd_is_finite())),
        always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        always(lift_state(Cluster::there_is_the_controller_state(controller_id))),
        always(lift_state(Cluster::there_is_no_request_msg_to_external(controller_id))),
        always(lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id))),
        always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::Init))))),
        always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::AfterListPods))))),
        always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), unwrap_local_state_closure(
            |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()
        ))))),
        always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), unwrap_local_state_closure(
            |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
        )))))
    );
}

pub proof fn spec_entails_all_invariants(spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
    ensures spec.entails(derived_invariants_since_beginning(vrs, cluster, controller_id)),
{
    cluster.lemma_always_every_in_flight_msg_has_unique_id(spec);
    cluster.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    cluster.lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_builtin_object_in_etcd_is_well_formed(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>(spec);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(spec, controller_id);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    lemma_always_vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(spec, vrs, cluster, controller_id);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(spec, controller_id);
    cluster.lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_every_ongoing_reconcile_has_lower_id_than_allocator(spec, controller_id);
    cluster.lemma_always_ongoing_reconciles_is_finite(spec, controller_id);
    cluster.lemma_always_etcd_is_finite(spec);
    assert forall |vrs: VReplicaSetView| spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, #[trigger] vrs.object_ref())))) by {
        cluster.lemma_always_pending_req_of_key_is_unique_with_unique_id(spec, controller_id, vrs.object_ref());
    }
    spec_entails_always_tla_forall(spec, |vrs: VReplicaSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())));
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    // TODO: not yet proved, should be included in non-interference property and (further) constrained in state_machine.rs
    assume(spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external(controller_id)))));
    cluster.lemma_always_cr_states_are_unmarshallable::<VReplicaSetReconciler, VReplicaSetReconcileState, VReplicaSetView, VoidEReqView, VoidERespView>(spec, controller_id);
    VReplicaSetReconcileState::marshal_preserves_integrity();
    assert forall |vrs: VReplicaSetView| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::Init))))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::Init));
    }
    spec_entails_always_tla_forall(spec, |vrs: VReplicaSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::Init))));
    assert forall |vrs: VReplicaSetView| spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, #[trigger] vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::AfterListPods))))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::AfterListPods));
    }
    spec_entails_always_tla_forall(spec, |vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::AfterListPods))));
    assert forall |vrs: VReplicaSetView| spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), unwrap_local_state_closure(
        |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()
    ))))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, vrs.object_ref(), unwrap_local_state_closure(|s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()));
    }
    spec_entails_always_tla_forall(spec, |vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), unwrap_local_state_closure(
        |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()
    ))));
    assert forall |vrs: VReplicaSetView| spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), unwrap_local_state_closure(
        |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
    ))))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, vrs.object_ref(), unwrap_local_state_closure(|s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()));
    }
    spec_entails_always_tla_forall(spec, |vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), unwrap_local_state_closure(
        |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
    ))));
    entails_always_and_n!(
        spec,
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)),
        lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)),
        lift_state(Cluster::etcd_is_finite()),
        tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref()))),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::there_is_no_request_msg_to_external(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)),
        tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::Init)))),
        tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::AfterListPods)))),
        tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), unwrap_local_state_closure(
            |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()
        )))),
        tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), unwrap_local_state_closure(
            |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
        ))))
    );
}
}