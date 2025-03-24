use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*,
    proof::lemma_true_leads_to_always_the_object_in_reconcile_has_spec_and_uid_as
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
    proof::{helper_invariants::{predicate::*}, helper_lemmas, liveness::*, predicate::*},
};
use vstd::{map::*, map_lib::*, math::*, prelude::*};

verus! {

pub open spec fn assumption_and_invariants_of_all_phases(vrs: VReplicaSetView) -> TempPred<ClusterState> {
    invariants(vrs)
    .and(always(lift_state(desired_state_is(vrs))))
    .and(invariants_since_phase_i(vrs))
    .and(invariants_since_phase_ii(vrs))
    .and(invariants_since_phase_iii(vrs))
    .and(invariants_since_phase_iv(vrs))
    .and(invariants_since_phase_v(vrs))
    .and(invariants_since_phase_vi(vrs))
    .and(invariants_since_phase_vii(vrs))
}

pub open spec fn invariants_since_phase_n(n: nat, vrs: VReplicaSetView) -> TempPred<ClusterState> {
    if n == 0 {
        invariants(vrs).and(always(lift_state(desired_state_is(vrs))))
    } else if n == 1 {
        invariants_since_phase_i(vrs)
    } else if n == 2 {
        invariants_since_phase_ii(vrs)
    } else if n == 3 {
        invariants_since_phase_iii(vrs)
    } else if n == 4 {
        invariants_since_phase_iv(vrs)
    } else if n == 5 {
        invariants_since_phase_v(vrs)
    } else if n == 6 {
        invariants_since_phase_vi(vrs)
    } else if n == 7 {
        invariants_since_phase_vii(vrs)
    } else {
        true_pred()
    }
}

pub open spec fn spec_before_phase_n(n: nat, vrs: VReplicaSetView) -> TempPred<ClusterState>
    decreases n,
{
    if n == 1 {
        invariants(vrs).and(always(lift_state(desired_state_is(vrs))))
    } else if 2 <= n <= 8 {
        spec_before_phase_n((n-1) as nat, vrs).and(invariants_since_phase_n((n-1) as nat, vrs))
    } else {
        true_pred()
    }
}

#[verifier(external_body)]
pub proof fn spec_of_previous_phases_entails_eventually_new_invariants(vrs: VReplicaSetView, cluster: Cluster, controller_id: int, cr: T, i: nat)
    requires 1 <= i <= 7,
    ensures spec_before_phase_n(i, vrs).entails(true_pred().leads_to(invariants_since_phase_n(i, vrs))),
{
    let spec = spec_before_phase_n(i, vrs);
    reveal_with_fuel(spec_before_phase_n, 8);
    if i == 1 {
        Cluster::lemma_true_leads_to_crash_always_disabled(spec, controller_id);
        Cluster::lemma_true_leads_to_req_drop_always_disabled(spec);
        Cluster::lemma_true_leads_to_always_the_object_in_schedule_has_spec_and_uid_as(spec, controller_id, cr);
        Cluster::lemma_always_there_is_the_controller_state(spec, controller_id);
        leads_to_always_combine_n!(
            spec,
            true_pred(),
            lift_state(Cluster::crash_disabled(controller_id)),
            lift_state(Cluster::req_drop_disabled()),
            lift_state(Cluster::pod_monkey_disabled())
        );
    } else {
        terminate::reconcile_eventually_terminates(spec, controller_id);
        if i == 2 {
            lemma_true_leads_to_always_the_object_in_reconcile_has_spec_and_uid_as(spec, controller_id);
        } else if i == 3 {
            Cluster::lemma_eventually_always_every_create_request_is_well_formed(spec, cluster, controller_id);
            Cluster::lemma_eventually_always_no_pending_update_or_update_status_request_on_pods(spec, cluster, controller_id);
            Cluster::lemma_eventually_always_no_pending_create_or_delete_request_not_from_controller_on_pods(spec, cluster, conatroller_id);
            
        } else if i == 4 {
            Cluster::lemma_eventually_always_garbage_collector_does_not_delete_vrs_pods(spec, vrs, cluster, controller_id);
            Cluster::lemma_eventually_always_every_create_matching_pod_request_implies_at_after_create_pod_step(spec, vrs, cluster, controller_id)
            Cluster::lemma_eventually_always_every_delete_matching_pod_request_implies_at_after_delete_pod_step(spec, vrs, cluster, controller_id)
            Cluster::lemma_eventually_always_each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(vrs, cluster, controller_id)
        } else if i == 5 {
            Cluster::lemma_eventually_always_every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, cluster, controller_id)
        }
    }
}

pub open spec fn derived_invariants_since_beginning(cluster: Cluster) -> TempPred<ClusterState> {
    always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())))
    .and(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())))
    .and(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>())))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id))))
    .and(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())))
    .and(always(lift_state(vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp)))
    .and(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())))
    .and(always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id))))
    .and(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs))))
    .and(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))))
    .and(always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id))))
    .and(always(lift_state(Cluster::etcd_is_finite())))
    .and(Cluster::lemma_always_pending_req_of_key_is_unique_with_unique_id(spec, controller_id, vrs.object_ref()))
}

}