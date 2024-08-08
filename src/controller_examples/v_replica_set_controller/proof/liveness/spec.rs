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
    .and(true_pred() /* invariants_since_phase_i(vrs) */)
    .and(true_pred() /* invariants_since_phase_ii(vrs) */)
    .and(true_pred() /* invariants_since_phase_iii(vrs) */)
    .and(true_pred() /* invariants_since_phase_iv(vrs) */)
    .and(true_pred() /* invariants_since_phase_v(vrs) */)
    .and(true_pred() /* invariants_since_phase_vi(vrs) */)
    .and(true_pred() /* invariants_since_phase_vii(vrs) */)
}

pub open spec fn invariants_since_phase_n(n: nat, vrs: VReplicaSetView) -> TempPred<VRSCluster> {
    if n == 0 {
        invariants(vrs).and(always(lift_state(desired_state_is(vrs))))
    } else if n == 1 {
        true_pred() // invariants_since_phase_i(vrs)
    } else if n == 2 {
        true_pred() // invariants_since_phase_ii(vrs)
    } else if n == 3 {
        true_pred() // invariants_since_phase_iii(vrs)
    } else if n == 4 {
        true_pred() // invariants_since_phase_iv(vrs)
    } else if n == 5 {
        true_pred() // invariants_since_phase_v(vrs)
    } else if n == 6 {
        true_pred() // invariants_since_phase_vi(vrs)
    } else if n == 7 {
        true_pred() // invariants_since_phase_vii(vrs)
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
    .and(always(tla_forall(|k : usize| lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterCreatePod(k)))))))
    .and(always(tla_forall(|k : usize| lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterDeletePod(k)))))))
}

pub proof fn sm_spec_entails_all_invariants(vrs: VReplicaSetView)
    ensures cluster_spec().entails(derived_invariants_since_beginning(vrs)),
{
    assume(false);
}

}
