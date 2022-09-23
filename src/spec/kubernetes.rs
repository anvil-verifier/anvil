// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::{exists, requires, ensures, equal};
#[allow(unused_imports)]
use crate::apis::*;
#[allow(unused_imports)]
use crate::common::*;
#[allow(unused_imports)]
use crate::pervasive::{*, option::Option, set::*};
#[allow(unused_imports)]
use crate::custom_controller_logic::*;


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

    /// pending_api_watch_notification is the watch notification that
    /// should be sent to the controller
    /// There is no watch notification if the controller's request does not change any state
    /// (e.g., deleting a non-existing object)
    /// Kubernetes has to send out this watch notifiaction before handling the next request
    pub pending_api_watch_notification: Option<APIWatchNotification>,
}

impl KubernetesVariables {
    #[spec] #[verifier(publish)]
    pub fn well_formed(&self, c:KubernetesConstants) -> bool {
        self.cluster_state.well_formed()
        && match self.pending_api_watch_notification {
            Option::None => true,
            Option::Some(api_watch_notification) => api_watch_notification.well_formed(),
        }
    }
}

pub enum KubernetesStep {
    HandleWorkloadSubmissionStep,
    HandleAPIOpRequestStep,
    SendAPIWatchNotificationStep,
}

#[spec] #[verifier(publish)]
pub fn init(c: KubernetesConstants, v: KubernetesVariables) -> bool {
    c.well_formed()
    && v.well_formed(c)
    && v.cluster_state.empty()
    && equal(v.pending_api_watch_notification, Option::None)
}

#[spec] #[verifier(publish)]
pub fn all_well_formed(c: KubernetesConstants, v: KubernetesVariables, v_prime: KubernetesVariables, message_ops: MessageOps) -> bool {
    c.well_formed()
    && v.well_formed(c)
    && v_prime.well_formed(c)
    && message_ops.well_formed()
}

#[spec] #[verifier(publish)]
pub fn kubernetes_api_op_result(cluster_state: ClusterState, cluster_state_prime: ClusterState, api_op: APIOp) -> bool {
    match api_op {
        APIOp::Get{object_key} => cluster_state.contains(object_key),
        APIOp::Create{object_key, object} => !cluster_state.contains(object_key),
        APIOp::Update{object_key, object} => cluster_state.contains(object_key),
        APIOp::Delete{object_key} => cluster_state.contains(object_key),
        _ => false,
    }
}

#[spec] #[verifier(publish)]
pub fn handle_workload_submission(c: KubernetesConstants, v: KubernetesVariables, v_prime: KubernetesVariables, message_ops: MessageOps) -> bool {

    all_well_formed(c, v, v_prime, message_ops)
    && equal(v.pending_api_watch_notification, Option::None)
    && match message_ops.recv {
        Option::None => false,
        Option::Some(message_to_recv) => {
            match message_to_recv {
                Message::WorkloadSubmission(api_op_request) => {
                    let success = kubernetes_api_op_result(v.cluster_state, v_prime.cluster_state, api_op_request.api_op);
                    if success {
                        match api_op_request.api_op {
                            APIOp::Create{object_key, object} =>
                                is_cr_type(object_key.object_type)
                                && equal(v_prime.pending_api_watch_notification, Option::Some(APIWatchNotification{
                                    object: object,
                                    delta_type: WatchDeltaType::Create,
                                }))
                                && state_transition_by_api_op(v.cluster_state, v_prime.cluster_state, api_op_request.api_op),
                            APIOp::Update{object_key, object} =>
                                is_cr_type(object_key.object_type)
                                && equal(v_prime.pending_api_watch_notification, Option::Some(APIWatchNotification{
                                    object: object,
                                    delta_type: WatchDeltaType::Update,
                                }))
                                && state_transition_by_api_op(v.cluster_state, v_prime.cluster_state, api_op_request.api_op),
                            APIOp::Delete{object_key} =>
                                is_cr_type(object_key.object_type)
                                && equal(v_prime.pending_api_watch_notification, Option::Some(APIWatchNotification{
                                    object: v.cluster_state.get(object_key),
                                    delta_type: WatchDeltaType::Delete,
                                }))
                                && state_transition_by_api_op(v.cluster_state, v_prime.cluster_state, api_op_request.api_op),
                            _ => false,
                        }
                    } else {
                        equal(v_prime.pending_api_watch_notification, Option::None)
                        && equal(v.cluster_state, v_prime.cluster_state)
                    }
                },
                _ => false,
            }
        }
    }
    && equal(message_ops.send, Option::None)
}

#[spec] #[verifier(publish)]
pub fn handle_api_op_request(c: KubernetesConstants, v: KubernetesVariables, v_prime: KubernetesVariables, message_ops: MessageOps) -> bool {
    // TODO: we should consider the chain reaction
    // For example, creating a statefulset will lead to mulitple pod creation
    // There could be many such chain reactions caused by the Kubernetes core controllers
    // We might need to consider to implement a host for each core controller
    // to discover every possible interleaving between these controllers
    
    // TODO: we should allow processing api op while there are pending responses
    all_well_formed(c, v, v_prime, message_ops)
    && equal(v.pending_api_watch_notification, Option::None)
    && match message_ops.recv {
        Option::None => false,
        Option::Some(message_to_recv) => {
            match message_to_recv {
                Message::APIOpRequest(api_op_request) => {
                    // We should also validate whether this transition is allowed
                    let success = kubernetes_api_op_result(v.cluster_state, v_prime.cluster_state, api_op_request.api_op);
                    if success {
                        match api_op_request.api_op {
                            APIOp::Get{object_key} =>
                                equal(v_prime.pending_api_watch_notification, Option::None)
                                && equal(v.cluster_state, v_prime.cluster_state)
                                && equal(message_ops.send, Option::Some(Message::APIOpResponse(APIOpResponse{
                                    success:success,
                                    api_op:api_op_request.api_op,
                                    object:v.cluster_state.get(object_key),
                                }))),
                            APIOp::Create{object_key, object} =>
                                equal(v_prime.pending_api_watch_notification, Option::Some(APIWatchNotification{
                                    object: object,
                                    delta_type: WatchDeltaType::Create,
                                }))
                                && state_transition_by_api_op(v.cluster_state, v_prime.cluster_state, api_op_request.api_op)
                                && equal(message_ops.send, Option::Some(Message::APIOpResponse(APIOpResponse{
                                    success:success,
                                    api_op:api_op_request.api_op,
                                    object:object,
                                }))),
                            APIOp::Update{object_key, object} =>
                                equal(v_prime.pending_api_watch_notification, Option::Some(APIWatchNotification{
                                    object: object,
                                    delta_type: WatchDeltaType::Update,
                                }))
                                && state_transition_by_api_op(v.cluster_state, v_prime.cluster_state, api_op_request.api_op)
                                && equal(message_ops.send, Option::Some(Message::APIOpResponse(APIOpResponse{
                                    success:success,
                                    api_op:api_op_request.api_op,
                                    object:object,
                                }))),
                            APIOp::Delete{object_key} =>
                                equal(v_prime.pending_api_watch_notification, Option::Some(APIWatchNotification{
                                    object: v.cluster_state.get(object_key),
                                    delta_type: WatchDeltaType::Delete,
                                }))
                                && state_transition_by_api_op(v.cluster_state, v_prime.cluster_state, api_op_request.api_op)
                                && equal(message_ops.send, Option::Some(Message::APIOpResponse(APIOpResponse{
                                    success:success,
                                    api_op:api_op_request.api_op,
                                    object:v.cluster_state.get(object_key),
                                }))),
                            _ => false,
                        }
                    } else {
                        equal(v_prime.pending_api_watch_notification, Option::None)
                        && equal(v.cluster_state, v_prime.cluster_state)
                        && equal(message_ops.send, Option::Some(Message::APIOpResponse(APIOpResponse{
                            success:success,
                            api_op:api_op_request.api_op,
                            object:KubernetesObject::None,
                        })))
                    }
                },
                _ => false,
            }
        }
    }
}

#[spec] #[verifier(publish)]
pub fn send_api_watch_notification(c: KubernetesConstants, v: KubernetesVariables, v_prime: KubernetesVariables, message_ops: MessageOps) -> bool {
    all_well_formed(c, v, v_prime, message_ops)
    && equal(v, KubernetesVariables{
        pending_api_watch_notification: v.pending_api_watch_notification,
        ..v_prime
    })
    && !equal(v.pending_api_watch_notification, Option::None)
    && equal(v_prime.pending_api_watch_notification, Option::None)
    && equal(message_ops.recv, Option::None)
    && match message_ops.send {
        Option::None => false,
        Option::Some(message_to_send) => {
            match message_to_send {
                Message::APIWatchNotification(api_watch_notification) => equal(Option::Some(api_watch_notification), v.pending_api_watch_notification),
                _ => false,
            }
        }
    }
}

#[spec] #[verifier(publish)]
pub fn next_step(c: KubernetesConstants, v: KubernetesVariables, v_prime: KubernetesVariables, message_ops: MessageOps, step: KubernetesStep) -> bool {
    match step {
        KubernetesStep::HandleWorkloadSubmissionStep => handle_workload_submission(c, v, v_prime, message_ops),
        KubernetesStep::HandleAPIOpRequestStep => handle_api_op_request(c, v, v_prime, message_ops),
        KubernetesStep::SendAPIWatchNotificationStep => send_api_watch_notification(c, v, v_prime, message_ops),
    }
}

#[spec] #[verifier(publish)]
pub fn next(c: KubernetesConstants, v: KubernetesVariables, v_prime: KubernetesVariables, message_ops: MessageOps) -> bool {
    exists(|step: KubernetesStep| next_step(c, v, v_prime, message_ops, step))
}
