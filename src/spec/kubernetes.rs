// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#![allow(unused_imports)]
use crate::apis::*;
use crate::common::*;
use crate::custom_controller_logic::*;
use crate::pervasive::{option::*, set::*};
use builtin::*;
use builtin_macros::*;

verus! {

pub struct KubernetesConstants {

}

impl KubernetesConstants {
    #[spec] #[verifier(publish)]
    pub fn well_formed(&self) -> bool {
        true
    }
}

/// This Kubernetes is used to modeling etcd and the API server in a real Kubernetes cluster
/// Here we simplify the Kubernetes model a lot:
/// It receives one request and updates the cluster state (which is a map),
/// replies to the controller with one response
/// and notifies the controller of the new update (if any) made by the request
/// After that, Kubernetes can handle the next request
///
/// It does NOT support concurrent request handling for now
///
/// There are many other complexity we need to consider later, including:
/// - Concurrent request handling, i.e., using a queue for storing pending response
/// - The cache layer at the API server
/// - Admission control (e.g., webhook)
/// - More error types when a request fails
/// - Chain reactions (or, core controllers), like creating a statefulset will lead to many pod creations
/// - ...
pub struct KubernetesVariables {
    /// cluster_state is a huge map that contains all the core and custom objects in Kubernetes
    /// It is supposed to model the etcd in a real Kubernetes cluster
    /// Here in the Kubernetes model, cluster_state is updated upon each API Op request
    /// from the controller or client
    pub cluster_state: ClusterState,

    /// pending_api_event_notification is the watch notification that
    /// should be sent to the controller
    /// There is no watch notification if the controller's request does not change any state
    /// (e.g., deleting a non-existing object)
    /// Kubernetes has to send out this watch notification before handling the next request
    pub pending_api_event_notification: Option<APIEventNotification>,
}

impl KubernetesVariables {
    #[spec] #[verifier(publish)]
    pub fn well_formed(&self, c:KubernetesConstants) -> bool {
        self.cluster_state.well_formed()
        && (self.pending_api_event_notification.is_None()
            || (self.pending_api_event_notification.is_Some() && self.pending_api_event_notification.get_Some_0().well_formed()))
    }
}

pub enum KubernetesStep {
    // HandleWorkloadSubmissionStep,
    HandleAPIOpRequestStep,
    SendAPIWatchNotificationStep,
}

#[spec] #[verifier(publish)]
pub fn init(c: KubernetesConstants, v: KubernetesVariables) -> bool {
    c.well_formed()
    && v.well_formed(c)
    && v.cluster_state.empty()
    && v.pending_api_event_notification.is_None()
}

#[spec] #[verifier(publish)]
pub fn all_well_formed(c: KubernetesConstants, v: KubernetesVariables, v_prime: KubernetesVariables, network_ops: NetworkOps) -> bool {
    c.well_formed()
    && v.well_formed(c)
    && v_prime.well_formed(c)
    && network_ops.well_formed()
}

#[spec] #[verifier(publish)]
pub fn kubernetes_api_op_result(cluster_state: ClusterState, cluster_state_prime: ClusterState, api_op: APIOp) -> bool {
    match api_op {
        APIOp::Get{object_key} => cluster_state.contains(object_key),
        APIOp::Create{object_key, object} => !cluster_state.contains(object_key),
        APIOp::Update{object_key, object} => cluster_state.contains(object_key),
        APIOp::Delete{object_key} => cluster_state.contains(object_key),
    }
}

#[spec] #[verifier(publish)]
pub fn handle_api_op_request(c: KubernetesConstants, v: KubernetesVariables, v_prime: KubernetesVariables, network_ops: NetworkOps) -> bool {
    // TODO: we should consider the chain reaction
    // For example, creating a statefulset will lead to mulitple pod creation
    // There could be many such chain reactions caused by the Kubernetes core controllers
    // We might need to consider to implement a host for each core controller
    // to discover every possible interleaving between these controllers

    // TODO: we should allow processing api op while there are pending responses
    all_well_formed(c, v, v_prime, network_ops)
    && v.pending_api_event_notification.is_None()
    && network_ops.recv.is_Some()
    && (network_ops.recv.get_Some_0().src === HostId::CustomController || network_ops.recv.get_Some_0().src === HostId::CustomClient)
    && network_ops.recv.get_Some_0().dst === HostId::KubernetesAPI
    && match network_ops.recv.get_Some_0().payload {
        Payload::APIOpRequest(api_op_request) => {
            network_ops.send.is_Some()
            && network_ops.send.get_Some_0().src === HostId::KubernetesAPI
            && network_ops.send.get_Some_0().dst === network_ops.recv.get_Some_0().src
            && match network_ops.send.get_Some_0().payload {
                Payload::APIOpResponse(api_op_response) => {
                    let success = kubernetes_api_op_result(v.cluster_state, v_prime.cluster_state, api_op_request.api_op);
                    api_op_response.success === success
                    && api_op_response.api_op_request === api_op_request
                    && if success {
                        match api_op_request.api_op {
                            APIOp::Get{object_key} =>
                                v.cluster_state.get(object_key).is_Some()
                                && v_prime.pending_api_event_notification.is_None()
                                && v.cluster_state === v_prime.cluster_state
                                && api_op_response.optional_object === v.cluster_state.get(object_key),
                            APIOp::Create{object_key, object} =>
                                v.cluster_state.get(object_key).is_None()
                                && v_prime.pending_api_event_notification === Option::Some(APIEventNotification{
                                    api_event: APIEvent::Added{
                                        object_key: object_key,
                                        object: object,
                                    }
                                })
                                && state_transition_by_api_op(v.cluster_state, v_prime.cluster_state, api_op_request.api_op)
                                && api_op_response.optional_object === Option::Some(object),
                            APIOp::Update{object_key, object} =>
                                v.cluster_state.get(object_key).is_Some()
                                && v_prime.pending_api_event_notification === Option::Some(APIEventNotification{
                                    api_event: APIEvent::Modified{
                                        object_key: object_key,
                                        object: object,
                                    }
                                })
                                && state_transition_by_api_op(v.cluster_state, v_prime.cluster_state, api_op_request.api_op)
                                && api_op_response.optional_object === Option::Some(object),
                            APIOp::Delete{object_key} =>
                                v.cluster_state.get(object_key).is_Some()
                                && v_prime.pending_api_event_notification === Option::Some(APIEventNotification{
                                    api_event: APIEvent::Deleted{
                                        object_key: object_key,
                                        object: v.cluster_state.get(object_key).get_Some_0(),
                                    }
                                })
                                && state_transition_by_api_op(v.cluster_state, v_prime.cluster_state, api_op_request.api_op)
                                && api_op_response.optional_object === v.cluster_state.get(object_key),
                        }
                    } else {
                        v_prime.pending_api_event_notification.is_None()
                        && v.cluster_state === v_prime.cluster_state
                        && api_op_response.optional_object.is_None()
                    }
                },
                _ => false,
            }
        },
        _ => false,
    }
}

#[spec] #[verifier(publish)]
pub fn send_api_event_notification(c: KubernetesConstants, v: KubernetesVariables, v_prime: KubernetesVariables, network_ops: NetworkOps) -> bool {
    all_well_formed(c, v, v_prime, network_ops)
    && v === KubernetesVariables{
        pending_api_event_notification: v.pending_api_event_notification,
        ..v_prime
    }
    && v.pending_api_event_notification !== Option::None
    && v_prime.pending_api_event_notification === Option::None
    && network_ops.recv.is_None()
    && network_ops.send.is_Some()
    && network_ops.send.get_Some_0().src === HostId::KubernetesAPI
    && network_ops.send.get_Some_0().dst === HostId::CustomController
    && match network_ops.send.get_Some_0().payload {
        Payload::APIEventNotification(api_event_notification) => Option::Some(api_event_notification) === v.pending_api_event_notification,
        _ => false,
    }
}

#[spec] #[verifier(publish)]
pub fn next_step(c: KubernetesConstants, v: KubernetesVariables, v_prime: KubernetesVariables, network_ops: NetworkOps, step: KubernetesStep) -> bool {
    match step {
        // KubernetesStep::HandleWorkloadSubmissionStep => handle_workload_submission(c, v, v_prime, network_ops),
        KubernetesStep::HandleAPIOpRequestStep => handle_api_op_request(c, v, v_prime, network_ops),
        KubernetesStep::SendAPIWatchNotificationStep => send_api_event_notification(c, v, v_prime, network_ops),
    }
}

#[spec] #[verifier(publish)]
pub fn next(c: KubernetesConstants, v: KubernetesVariables, v_prime: KubernetesVariables, network_ops: NetworkOps) -> bool {
    exists(|step: KubernetesStep| next_step(c, v, v_prime, network_ops, step))
}

}
