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
    proof::{helper_invariants::{predicate::*, proof::*}, helper_lemmas, liveness::*, predicate::*},
};
use vstd::{map::*, map_lib::*, math::*, prelude::*};

verus! {

pub open spec fn assumption_and_invariants_of_all_phases(vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    invariants(vrs, cluster, controller_id)
    .and(always(lift_state(Cluster::desired_state_is(vrs))))
    .and(invariants_since_phase_i(controller_id))
    .and(invariants_since_phase_ii(controller_id, vrs))
    .and(invariants_since_phase_iii(vrs, cluster, controller_id))
    .and(invariants_since_phase_iv(vrs, cluster, controller_id))
    .and(invariants_since_phase_v(vrs, cluster, controller_id))
}

pub proof fn assumption_and_invariants_of_all_phases_is_stable(vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    ensures
        valid(stable(assumption_and_invariants_of_all_phases(vrs, cluster, controller_id))),
        valid(stable(invariants(vrs, cluster, controller_id))),
        forall |i: nat| 0 <= i <= 5 ==> valid(stable(#[trigger] spec_before_phase_n(i, vrs, cluster, controller_id))),
{
    reveal_with_fuel(spec_before_phase_n, 5);
    invariants_is_stable(vrs, cluster, controller_id);
    always_p_is_stable(lift_state(Cluster::desired_state_is(vrs)));
    invariants_since_phase_i_is_stable(controller_id);
    invariants_since_phase_ii_is_stable(controller_id, vrs);
    invariants_since_phase_iii_is_stable(vrs, cluster, controller_id);
    invariants_since_phase_iv_is_stable(vrs, cluster, controller_id);
    invariants_since_phase_v_is_stable(vrs, cluster, controller_id);
    stable_and_n!(
        invariants(vrs, cluster, controller_id),
        always(lift_state(Cluster::desired_state_is(vrs))),
        invariants_since_phase_i(controller_id),
        invariants_since_phase_ii(controller_id, vrs),
        invariants_since_phase_iii(vrs, cluster, controller_id),
        invariants_since_phase_iv(vrs, cluster, controller_id),
        invariants_since_phase_v(vrs, cluster, controller_id)
    );
}

pub open spec fn invariants_since_phase_n(n: nat, vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    if n == 0 {
        invariants(vrs, cluster, controller_id)
        .and(always(lift_state(Cluster::desired_state_is(vrs))))
    } else if n == 1 {
        invariants_since_phase_i(controller_id)
    } else if n == 2 {
        invariants_since_phase_ii(controller_id, vrs)
    } else if n == 3 {
        invariants_since_phase_iii(vrs, cluster, controller_id)
    } else if n == 4 {
        invariants_since_phase_iv(vrs, cluster, controller_id)
    } else if n == 5 {
        invariants_since_phase_v(vrs, cluster, controller_id)
    } else {
        true_pred()
    }
}

pub open spec fn spec_before_phase_n(n: nat, vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
    decreases n,
{
    if n == 1 {
        invariants(vrs, cluster, controller_id).and(always(lift_state(Cluster::desired_state_is(vrs))))
    } else if 2 <= n <= 6 {
        spec_before_phase_n((n-1) as nat, vrs, cluster, controller_id).and(invariants_since_phase_n((n-1) as nat, vrs, cluster, controller_id))
    } else {
        true_pred()
    }
}

pub open spec fn invariants_since_phase_i(controller_id: int) -> TempPred<ClusterState> {
    always(lift_state(Cluster::crash_disabled(controller_id)))
    .and(always(lift_state(Cluster::req_drop_disabled())))
    .and(always(lift_state(Cluster::pod_monkey_disabled())))
}

pub proof fn invariants_since_phase_i_is_stable(controller_id: int)
    ensures valid(stable(invariants_since_phase_i(controller_id))),
{
    stable_and_always_n!(
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled())
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
}

pub proof fn invariants_since_phase_iii_is_stable(vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants_since_phase_iii(vrs, cluster, controller_id))),
{
    stable_and_always_n!(
        lift_state(no_pending_update_or_update_status_request_on_pods()),
        lift_state(no_pending_create_or_delete_request_not_from_controller_on_pods())
    );
}

pub open spec fn invariants_since_phase_iv(vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(garbage_collector_does_not_delete_vrs_pods(vrs)))
    .and(always(lift_state(every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id))))
    .and(always(lift_state(every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id))))
    .and(always(lift_state(each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id))))
}

pub proof fn invariants_since_phase_iv_is_stable(vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants_since_phase_iv(vrs, cluster, controller_id))),
{
    stable_and_always_n!(
        lift_state(garbage_collector_does_not_delete_vrs_pods(vrs)),
        lift_state(every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)),
        lift_state(every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)),
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
    always_p_is_stable(lift_state(every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)));
}

pub proof fn spec_of_previous_phases_entails_eventually_new_invariants(vrs: VReplicaSetView, cluster: Cluster, controller_id: int, i: nat)
    requires 1 <= i <= 5,
    ensures spec_before_phase_n(i, vrs, cluster, controller_id).entails(true_pred().leads_to(invariants_since_phase_n(i, vrs, cluster, controller_id))),
{
    let spec = spec_before_phase_n(i, vrs, cluster, controller_id);
    reveal_with_fuel(spec_before_phase_n, 6);
    if i == 1 {
        cluster.lemma_true_leads_to_crash_always_disabled(spec, controller_id);
        cluster.lemma_true_leads_to_req_drop_always_disabled(spec);
        cluster.lemma_true_leads_to_always_the_object_in_schedule_has_spec_and_uid_as(spec, controller_id, vrs);
        cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
        leads_to_always_combine_n!(
            spec,
            true_pred(),
            lift_state(Cluster::crash_disabled(controller_id)),
            lift_state(Cluster::req_drop_disabled()),
            lift_state(Cluster::pod_monkey_disabled())
        );
    } else {
        terminate::reconcile_eventually_terminates(spec, cluster, controller_id);
        if i == 2 {
            cluster.lemma_true_leads_to_always_the_object_in_reconcile_has_spec_and_uid_as(spec, controller_id, vrs);
        } else if i == 3 {
            lemma_eventually_always_no_pending_update_or_update_status_request_on_pods(spec, cluster, controller_id);
            lemma_eventually_always_no_pending_create_or_delete_request_not_from_controller_on_pods(spec, cluster, controller_id);
        } else if i == 4 {
            lemma_eventually_always_garbage_collector_does_not_delete_vrs_pods(spec, vrs, cluster, controller_id);
            lemma_eventually_always_every_create_matching_pod_request_implies_at_after_create_pod_step(spec, vrs, cluster, controller_id);
            lemma_eventually_always_every_delete_matching_pod_request_implies_at_after_delete_pod_step(spec, vrs, cluster, controller_id);
            lemma_eventually_always_each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(spec, vrs, cluster, controller_id);
        } else if i == 5 {
            lemma_eventually_always_every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(spec, vrs, cluster, controller_id);
        }
    }
}

pub open spec fn next_with_wf(cluster: Cluster) -> TempPred<ClusterState> {
    always(lift_action(cluster.next()))
    .and(tla_forall(|input| cluster.api_server_next().weak_fairness(input)))
    .and(tla_forall(|input| cluster.builtin_controllers_next().weak_fairness(input)))
    .and(tla_forall(|input| cluster.controller_next().weak_fairness(input)))
    .and(tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness(input)))
    .and(tla_forall(|input| cluster.restart_controller().weak_fairness(input)))
    .and(tla_forall(|input| cluster.disable_crash().weak_fairness(input)))
    .and(tla_forall(|input| cluster.drop_req().weak_fairness(input)))
    .and(tla_forall(|input| cluster.pod_monkey_next().weak_fairness(input)))
    .and(tla_forall(|input| cluster.external_next().weak_fairness(input)))
    .and(cluster.disable_req_drop().weak_fairness(()))
    .and(cluster.disable_pod_monkey().weak_fairness(()))
    .and(cluster.stutter().weak_fairness(()))
}

pub proof fn next_with_wf_is_stable(cluster: Cluster)
    ensures valid(stable(next_with_wf(cluster))),
{
    always_p_is_stable(lift_action(cluster.next()));
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.api_server_next());
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.builtin_controllers_next());
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.controller_next());
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.schedule_controller_reconcile());
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.restart_controller());
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.disable_crash());
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.drop_req());
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.pod_monkey_next());
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.external_next());
    Cluster::action_weak_fairness_is_stable(cluster.disable_req_drop());
    Cluster::action_weak_fairness_is_stable(cluster.disable_pod_monkey());
    Cluster::action_weak_fairness_is_stable(cluster.stutter());
    stable_and_n!(
        always(lift_action(cluster.next())),
        tla_forall(|input| cluster.api_server_next().weak_fairness(input)),
        tla_forall(|input| cluster.builtin_controllers_next().weak_fairness(input)),
        tla_forall(|input| cluster.controller_next().weak_fairness(input)),
        tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness(input)),
        tla_forall(|input| cluster.restart_controller().weak_fairness(input)),
        tla_forall(|input| cluster.disable_crash().weak_fairness(input)),
        tla_forall(|input| cluster.drop_req().weak_fairness(input)),
        tla_forall(|input| cluster.pod_monkey_next().weak_fairness(input)),
        tla_forall(|input| cluster.external_next().weak_fairness(input)),
        cluster.disable_req_drop().weak_fairness(()),
        cluster.disable_pod_monkey().weak_fairness(()),
        cluster.stutter().weak_fairness(())
    );
}

// This predicate combines all the possible actions (next), weak fairness and invariants that hold throughout the execution.
// We name it invariants here because these predicates are never violated, thus they can all be seen as some kind of invariants.
//
// The final goal of our proof is to show init /\ invariants |= []desired_state_is(vrs) ~> []current_state_matches(vrs).
// init /\ invariants is equivalent to init /\ next /\ weak_fairness, so we get cluster_spec() |= []desired_state_is(vrs) ~> []current_state_matches(vrs).
pub open spec fn invariants(vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    next_with_wf(cluster).and(derived_invariants_since_beginning(vrs, cluster, controller_id))
}

pub proof fn invariants_is_stable(vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants(vrs, cluster, controller_id))),
{
    next_with_wf_is_stable(cluster);
    derived_invariants_since_beginning_is_stable(vrs, cluster, controller_id);
    stable_and_n!(
        next_with_wf(cluster),
        derived_invariants_since_beginning(vrs, cluster, controller_id)
    );
}

pub open spec fn derived_invariants_since_beginning(vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())))
    .and(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())))
    .and(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>())))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id))))
    .and(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())))
    .and(always(lift_state(vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id))))
    .and(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())))
    .and(always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id))))
    .and(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs))))
    .and(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))))
    .and(always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id))))
    .and(always(lift_state(Cluster::etcd_is_finite())))
    .and(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref()))))
}

pub proof fn derived_invariants_since_beginning_is_stable(vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(derived_invariants_since_beginning(vrs, cluster, controller_id))),
{
    stable_and_always_n!(
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id)),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)),
        lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref()))
    );
}
}