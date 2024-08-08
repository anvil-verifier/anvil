// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{map_lib::*, string_view::*};
use crate::v_replica_set_controller::{
    model::{reconciler::*},
    proof::{helper_invariants, predicate::*},
    trusted::{spec_types::*, step::*, liveness_theorem::*},
};
use vstd::{prelude::*, string::*};

verus! {

#[verifier(external_body)]
pub proof fn lemma_from_after_list_pods_step_to_after_scale_pod_step_or_done(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, diff: nat,
)
    ensures
        // Case 1: Number of matching pods is less than the replica count.
        diff > 0 ==> spec.entails(
            lift_state(|s: VRSCluster| {
                &&& num_fewer_pods_is(vrs, s.resources(), diff)
                &&& pending_req_in_flight_at_after_list_pods_step(vrs)(s)
            }).leads_to(lift_state(|s: VRSCluster| {
                &&& num_fewer_pods_is(vrs, s.resources(), (diff - 1) as nat)
                &&& pending_req_in_flight_at_after_create_pod_step(vrs, (diff - 1) as nat)(s)
            }))
        ),
        // Case 2: Number of matching pods is greater than the replica count.
        diff > 0 ==> spec.entails(
            lift_state(|s: VRSCluster| {
                &&& num_more_pods_is(vrs, s.resources(), diff)
                &&& pending_req_in_flight_at_after_list_pods_step(vrs)(s)
            }).leads_to(lift_state(|s: VRSCluster| {
                &&& num_more_pods_is(vrs, s.resources(), (diff - 1) as nat)
                &&& pending_req_in_flight_at_after_delete_pod_step(vrs, (diff - 1) as nat)(s)
            }))
        ),
        // Case 3: Number of matching pods equals the replica count.
        spec.entails(
            lift_state(|s: VRSCluster| {
                &&& num_more_pods_is(vrs, s.resources(), 0)
                &&& pending_req_in_flight_at_after_list_pods_step(vrs)(s)
            }).leads_to(lift_state(|s: VRSCluster| {
                &&& resource_state_matches(vrs, s.resources())
                &&& at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Done)(s)
            }))
        ),
{
}

#[verifier(external_body)]
pub proof fn lemma_from_after_create_pod_step_to_after_create_pod_step_or_done(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, diff: nat,
)
    ensures
        // Case 1: Number of matching pods is less than the replica count.
        diff > 0 ==> spec.entails(
            lift_state(|s: VRSCluster| {
                &&& num_fewer_pods_is(vrs, s.resources(), diff)
                &&& pending_req_in_flight_at_after_create_pod_step(vrs, diff)(s)
            }).leads_to(lift_state(|s: VRSCluster| {
                &&& num_fewer_pods_is(vrs, s.resources(), (diff - 1) as nat)
                &&& pending_req_in_flight_at_after_create_pod_step(vrs, (diff - 1) as nat)(s)
            }))
        ),
        // Case 2: No more pods to create.
        diff == 0 ==> spec.entails(
            lift_state(|s: VRSCluster| {
                &&& num_fewer_pods_is(vrs, s.resources(), 0)
                &&& pending_req_in_flight_at_after_create_pod_step(vrs, 0)(s)
            }).leads_to(lift_state(|s: VRSCluster| {
                &&& resource_state_matches(vrs, s.resources())
                &&& at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Done)(s)
            }))
        ),
{
}

#[verifier(external_body)]
pub proof fn lemma_from_after_delete_pod_step_to_after_delete_pod_step_or_done(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, diff: nat,
)
    ensures
        // Case 1: Number of matching pods is less than the replica count.
        diff > 0 ==> spec.entails(
            lift_state(|s: VRSCluster| {
                &&& num_more_pods_is(vrs, s.resources(), diff)
                &&& pending_req_in_flight_at_after_delete_pod_step(vrs, diff)(s)
            }).leads_to(lift_state(|s: VRSCluster| {
                &&& num_fewer_pods_is(vrs, s.resources(), (diff - 1) as nat)
                &&& pending_req_in_flight_at_after_delete_pod_step(vrs, (diff - 1) as nat)(s)
            }))
        ),
        // Case 2: No more pods to create.
        diff == 0 ==> spec.entails(
            lift_state(|s: VRSCluster| {
                &&& num_more_pods_is(vrs, s.resources(), 0)
                &&& pending_req_in_flight_at_after_delete_pod_step(vrs, 0)(s)
            }).leads_to(lift_state(|s: VRSCluster| {
                &&& resource_state_matches(vrs, s.resources())
                &&& at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Done)(s)
            }))
        ),
{
}


}
