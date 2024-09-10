// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::v_replica_set_controller::{
    model::reconciler::*,
    proof::{helper_invariants, liveness::terminate, predicate::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
use vstd::prelude::*;

verus! {

pub open spec fn assumption_and_invariants_of_all_phases(vrs: VReplicaSetView) -> TempPred<VRSCluster> {
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

pub open spec fn invariants_since_phase_n(n: nat, vrs: VReplicaSetView) -> TempPred<VRSCluster> {
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

pub open spec fn spec_before_phase_n(n: nat, vrs: VReplicaSetView) -> TempPred<VRSCluster>
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

pub proof fn assumption_and_invariants_of_all_phases_is_stable(vrs: VReplicaSetView)
    ensures
        valid(stable(assumption_and_invariants_of_all_phases(vrs))),
        valid(stable(invariants(vrs))),
        forall |i: nat|  1 <= i <= 8 ==> valid(stable(#[trigger] spec_before_phase_n(i, vrs))),
{
    assume(false)
}

// Next and all the wf conditions.
pub open spec fn next_with_wf() -> TempPred<VRSCluster> {
    always(lift_action(VRSCluster::next()))
    .and(tla_forall(|input| VRSCluster::kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| VRSCluster::external_api_next().weak_fairness(input)))
    .and(tla_forall(|input| VRSCluster::controller_next().weak_fairness(input)))
    .and(tla_forall(|input| VRSCluster::schedule_controller_reconcile().weak_fairness(input)))
    .and(tla_forall(|input| VRSCluster::builtin_controllers_next().weak_fairness(input)))
    .and(VRSCluster::disable_crash().weak_fairness(()))
    .and(VRSCluster::disable_transient_failure().weak_fairness(()))
}

/// This predicate combines all the possible actions (next), weak fairness and invariants that hold throughout the execution.
/// We name it invariants here because these predicates are never violated, thus they can all be seen as some kind of invariants.
///
/// The final goal of our proof is to show init /\ invariants |= []desired_state_is(cr) ~> []current_state_matches(cr).
/// init /\ invariants is equivalent to init /\ next /\ weak_fairness, so we get cluster_spec() |= []desired_state_is(cr) ~> []current_state_matches(cr).
pub open spec fn invariants(vrs: VReplicaSetView) -> TempPred<VRSCluster> {
    next_with_wf().and(derived_invariants_since_beginning(vrs))
}

// The safety invariants that are required to prove liveness.
pub open spec fn derived_invariants_since_beginning(vrs: VReplicaSetView) -> TempPred<VRSCluster> {
    always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterListPods)))))
    .and(always(lift_state(VRSCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(vrs.object_ref()))))
    .and(always(lift_state(VRSCluster::object_in_ok_get_response_has_smaller_rv_than_etcd())))
    .and(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref()))))
    .and(always(lift_state(VRSCluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(VRSCluster::each_object_in_etcd_is_well_formed())))
    .and(always(lift_state(VRSCluster::each_scheduled_object_has_consistent_key_and_valid_metadata())))
    .and(always(lift_state(VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())))
    .and(always(lift_state(VRSCluster::no_pending_req_msg_at_reconcile_state(vrs.object_ref(), |s: VReplicaSetReconcileState| s.reconcile_step == VReplicaSetReconcileStep::Init))))
    .and(always(tla_forall(|k : usize| lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterCreatePod(k)))))))
    .and(always(tla_forall(|k : usize| lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterDeletePod(k)))))))
    .and(always(lift_state(helper_invariants::cluster_resources_is_finite())))
    .and(always(lift_state(helper_invariants::vrs_replicas_bounded_above(vrs))))
    .and(always(lift_state(helper_invariants::vrs_selector_matches_template_labels(vrs))))
    .and(always(lift_state(helper_invariants::every_create_request_is_well_formed())))
    .and(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods())))
    .and(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs))))
    .and(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs))))
}

/// The first notable phase comes when crash and k8s busy are always disabled and the object in schedule always has the same
/// spec and uid as the cr we provide.
///
/// Note that don't try to find any connections between those invariants -- they are put together because they don't have to
/// wait for another of them to first be satisfied.
pub open spec fn invariants_since_phase_i(vrs: VReplicaSetView) -> TempPred<VRSCluster> {
    always(lift_state(VRSCluster::crash_disabled()))
    .and(always(lift_state(VRSCluster::busy_disabled())))
    .and(always(lift_state(VRSCluster::the_object_in_schedule_has_spec_and_uid_as(vrs))))
}

// Placeholder invariants -- will develop from the WF1 lemmas.
pub open spec fn invariants_since_phase_ii(vrs: VReplicaSetView) -> TempPred<VRSCluster> {
    true_pred()
}

pub open spec fn invariants_since_phase_iii(vrs: VReplicaSetView) -> TempPred<VRSCluster> {
    true_pred()
}

pub open spec fn invariants_since_phase_iv(vrs: VReplicaSetView) -> TempPred<VRSCluster> {
    true_pred()
}

pub open spec fn invariants_since_phase_v(vrs: VReplicaSetView) -> TempPred<VRSCluster> {
    true_pred()
}

pub open spec fn invariants_since_phase_vi(vrs: VReplicaSetView) -> TempPred<VRSCluster> {
    true_pred()
}

pub open spec fn invariants_since_phase_vii(vrs: VReplicaSetView) -> TempPred<VRSCluster> {
    true_pred()
}

pub proof fn sm_spec_entails_all_invariants(vrs: VReplicaSetView)
    ensures cluster_spec().entails(derived_invariants_since_beginning(vrs)),
{
    assume(false);
}

}
