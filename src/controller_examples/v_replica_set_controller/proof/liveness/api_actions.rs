// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*,
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
use vstd::{prelude::*, string::*, map::*, map_lib::*, math::abs};

verus! {

pub proof fn lemma_api_request_outside_create_or_delete_loop_maintains_matching_pods(
    s: VRSCluster, s_prime: VRSCluster, vrs: VReplicaSetView, diff: int, msg: VRSMessage,
)
    requires
        VRSCluster::next_step(s, s_prime, Step::ApiServerStep(Some(msg))),
        VRSCluster::crash_disabled()(s),
        VRSCluster::busy_disabled()(s),
        VRSCluster::every_in_flight_msg_has_unique_id()(s),
        VRSCluster::each_object_in_etcd_is_well_formed()(s),
        helper_invariants::every_create_request_is_well_formed()(s),
        helper_invariants::no_pending_update_or_update_status_request_on_pods()(s),
        helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)(s),
        helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)(s),
        forall |diff: usize| !(#[trigger] at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::AfterCreatePod(diff))(s)),
        forall |diff: usize| !(#[trigger] at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::AfterDeletePod(diff))(s)),
    ensures
        matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()),
{
    // Dispatch through all the requests which may mutate the k-v store.
    let mutates_key = if msg.content.is_create_request() {
        let req = msg.content.get_create_request();
        Some(ObjectRef{
            kind: req.obj.kind,
            name: if req.obj.metadata.name.is_Some() {
                req.obj.metadata.name.unwrap()
            } else {
                generate_name(s.kubernetes_api_state)
            },
            namespace: req.namespace,
        })
    } else if msg.content.is_delete_request() {
        let req = msg.content.get_delete_request();
        Some(req.key)
    } else if msg.content.is_update_request() {
        let req = msg.content.get_update_request();
        Some(req.key())
    } else if msg.content.is_update_status_request() {
        let req = msg.content.get_update_status_request();
        Some(req.key())
    } else {
        None
    };

    match mutates_key {
        Some(key) => {
            assert_maps_equal!(s.resources().remove(key) == s_prime.resources().remove(key));
            assert_maps_equal!(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));
        },
        _ => {}
    };
}

#[verifier(external_body)]
pub proof fn lemma_api_request_not_on_matching_pods_maintains_matching_pods(
    s: VRSCluster, s_prime: VRSCluster, vrs: VReplicaSetView, diff: int, msg: VRSMessage, req_msg: VRSMessage,
)
    requires
        msg != req_msg,
        req_msg == s.ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0(),
        VRSCluster::next_step(s, s_prime, Step::ApiServerStep(Some(msg))),
        VRSCluster::crash_disabled()(s),
        VRSCluster::busy_disabled()(s),
        VRSCluster::every_in_flight_msg_has_unique_id()(s),
        VRSCluster::each_object_in_etcd_is_well_formed()(s),
        helper_invariants::every_create_request_is_well_formed()(s),
        helper_invariants::no_pending_update_or_update_status_request_on_pods()(s),
        helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)(s),
        helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)(s),
    ensures
        matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources());
//
// @Xudong Sun take a look
//
// This is very similar to the proof above, but we'll need to explicitly handle the case that we're on
// an after create or delete pod step.
//

}
