// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use crate::common::*;
#[allow(unused_imports)]
use crate::pervasive::{*, option::Option};
#[allow(unused_imports)]
use crate::custom_controller_logic::*;
#[allow(unused_imports)]
use crate::dict::*;
#[allow(unused_imports)]
use crate::apis::*;

verus! {

pub struct ControllerConstants {
    pub controller_clock_upper_bound: int,
}

impl ControllerConstants {
    pub open spec fn well_formed(&self) -> bool {
        equal(self.controller_clock_upper_bound, controller_step_limit_spec())
    }
}

pub struct ControllerVariables {
    /// Reconcile_step represents the progress of the controller reconcile
    /// The verification framework only cares about three values:
    /// Init: the reconciliation cycle is about to start
    /// Done: the reconciliation cycle is finished successfully
    /// Retry: the reconciliation cycle failed due to some reason and should retry later
    pub reconcile_step: ReconcileStep,

    /// state_cache represents the controller's view of the cluster state
    /// Every kubernetes object in state_cache comes from the api op response
    ///
    /// This state_cache is NOT used to represent the local indexer which is updated by watch events
    /// Actually in kube-rs the controller never reads the local indexer
    /// and the controller always reads etcd through API server
    ///
    /// The state_cache is used to contain everything the controller
    /// has read (through API server to etcd) via Get/List/... inside each reconcile()
    ///
    /// Consider this statement that reads a pod into x: let x = podapi.Get(...)
    /// The state_cache is used to replace the x here (x will be an entry in state_cache)
    /// And the state_cache will be cleaned in end_reconcile()
    ///
    /// This might be a little bit counter-intuitive
    /// but note that we are spliting the entire reconcile() into atomic steps by each read/write to etcd
    /// so it is necessary to maintain what the controller has read so far in each reconcile using state_cache
    pub state_cache: ClusterState,

    /// in_reconcile means whether the controller is inside an ongoing reconciliation cycle
    /// It is set to true in start_reconcile
    /// and set to false in end_reconcile
    pub in_reconcile: bool,

    /// triggering_key points to the object that triggers the reconcile
    /// it is usually the cr object created/modified/deleted by the user
    /// It is set in receive_api_watch_notification (if triggered)
    /// and unset in end_reconcile
    /// It is better to be a list if we want to support concurrent reconciles later
    pub triggering_key: Option<ObjectKey>,

    /// last_api_op_response records the last api op response
    /// It is used as input of controller_reconcile_spec
    pub last_api_op_response: Option<APIOpResponse>,

    /// pending_api_op_request records the api op request that has not been finished
    /// The reconcile cannot continue if the pending request is not finished
    pub pending_api_op_request: Option<APIOpRequest>,

    pub controller_clock: int,

    pub before_receiving_response: bool,
}

impl ControllerVariables {
    pub open spec fn well_formed(&self, c:ControllerConstants) -> bool {
        self.state_cache.well_formed()
        && (self.last_api_op_response.is_None()
            || (self.last_api_op_response.is_Some() && self.last_api_op_response.get_Some_0().well_formed()))
        && (self.pending_api_op_request.is_None()
            || (self.pending_api_op_request.is_Some() && self.pending_api_op_request.get_Some_0().well_formed()))
    }
}

pub enum ControllerStep {
    ReceiveInformerUpdateStep,
    StartReconcileStep,
    ContinueReconcileStep,
    EndReconcileStep,
    ReceiveAPIOpResponseStep,
}

pub open spec fn init(c: ControllerConstants, v: ControllerVariables) -> bool {
    c.well_formed()
    && v.well_formed(c)
    && !v.in_reconcile
    && v.triggering_key.is_None()
    && v.reconcile_step === ReconcileStep::Init
    && v.state_cache.empty()
    && v.last_api_op_response.is_None()
    && v.pending_api_op_request.is_None()
    && v.controller_clock === c.controller_clock_upper_bound
    && !v.before_receiving_response
}

pub open spec fn all_well_formed(c: ControllerConstants, v: ControllerVariables, v_prime: ControllerVariables, message_ops: MessageOps) -> bool {
    c.well_formed()
    && v.well_formed(c)
    && v_prime.well_formed(c)
    && message_ops.well_formed()
}

/// receive_api_watch_notification does the following:
/// - receive the watch notification from the API server
/// - trigger reconcile if the event object is watched by the controller
///
/// We currently do not allow receiving api watch responses inside a reconcile
/// so we pose the constraints including:
/// * !v.in_reconcile
/// * equal(v.triggering_key, Option::None)
/// We do NOT update the state_cache here
/// The reason is that in kube-rs every watch event from the API server
/// will update the local indexer (in the informer) but the controller never reads the indexer
/// Note that this is very different from controller-runtime where the controller often
/// reads the local indexer (local cache)
pub open spec fn receive_api_watch_notification(c: ControllerConstants, v: ControllerVariables, v_prime: ControllerVariables, message_ops: MessageOps) -> bool {
    all_well_formed(c, v, v_prime, message_ops)
    && equal(v, ControllerVariables{
        triggering_key: v.triggering_key,
        ..v_prime
    })
    && !v.in_reconcile
    && !v.before_receiving_response
    && v.triggering_key.is_None()
    && v.pending_api_op_request.is_None()
    && v.last_api_op_response.is_None()
    && message_ops.send.is_None()
    && match message_ops.recv {
        Option::Some(Message::APIWatchNotification(api_watch_notification)) =>
            v_prime.triggering_key === map_to_triggering_key(api_watch_notification.object),
        _ => false
    }
}

/// start_reconcile does the following:
/// - Set in_reconcile to true and reconcile_step to Init to start reconcile
pub open spec fn start_reconcile(c: ControllerConstants, v: ControllerVariables, v_prime: ControllerVariables, message_ops: MessageOps) -> bool {
    all_well_formed(c, v, v_prime, message_ops)
    && v === ControllerVariables{
        in_reconcile: v.in_reconcile,
        last_api_op_response: v.last_api_op_response,
        ..v_prime
    }
    && !v.in_reconcile
    && v_prime.in_reconcile
    && !v.before_receiving_response
    && v.triggering_key.is_Some()
    && v.pending_api_op_request.is_None()
    && v.reconcile_step === ReconcileStep::Init
    && v.last_api_op_response.is_None()
    && v_prime.last_api_op_response === Option::Some(APIOpResponse{success:true, api_op_request:APIOpRequest{api_op: APIOp::Noop}, object:KubernetesObject::None})
    && message_ops.recv.is_None()
    && message_ops.send.is_None()
}

/// continue_reconcile does the following:
/// - Run one reconcile step (controller_logic_spec)
/// - Send the API Op request (if any) to Kubernetes
pub open spec fn continue_reconcile(c: ControllerConstants, v: ControllerVariables, v_prime: ControllerVariables, message_ops: MessageOps) -> bool {
    all_well_formed(c, v, v_prime, message_ops)
    && v.reconcile_step !== ReconcileStep::Done
    && v.reconcile_step !== ReconcileStep::Retry
    && message_ops.recv.is_None()
    && v.pending_api_op_request.is_None()
    && v.in_reconcile
    && v.controller_clock > 0
    && !v.before_receiving_response
    && v_prime.before_receiving_response
    && (v.controller_clock - 1) === v_prime.controller_clock
    && v.triggering_key.is_Some()
    && v.last_api_op_response.is_Some()
    && match message_ops.send {
        Option::None =>
            v === ControllerVariables{
                    reconcile_step: v.reconcile_step,
                    controller_clock: v.controller_clock,
                    before_receiving_response: v.before_receiving_response,
                    ..v_prime
                  }
            // We have no pending request since the controller_logic does not issue anything
            && v_prime.pending_api_op_request.is_None()
            && controller_logic_spec(v.reconcile_step, v.triggering_key.get_Some_0(), v.state_cache, v.last_api_op_response.get_Some_0(), v_prime.reconcile_step, v_prime.pending_api_op_request),
        Option::Some(message) => {
            match message {
                Message::APIOpRequest(api_op_request) =>
                    v === ControllerVariables{
                            reconcile_step: v.reconcile_step,
                            pending_api_op_request: v.pending_api_op_request,
                            controller_clock: v.controller_clock,
                            before_receiving_response: v.before_receiving_response,
                            ..v_prime
                         }
                    // We get a new pending request here
                    && v_prime.pending_api_op_request === Option::Some(api_op_request)
                    // We need to wait for new response for the new request from now
                    && controller_logic_spec(v.reconcile_step, v.triggering_key.get_Some_0(), v.state_cache, v.last_api_op_response.get_Some_0(), v_prime.reconcile_step, v_prime.pending_api_op_request),
                _ => false,
            }
        }
    }
}

/// receive_api_op_response does the following:
/// - Receive response of the API Op request sent by continue_reconcile
/// - Update the local cache of the cluster state based on the response
pub open spec fn receive_api_op_response(c: ControllerConstants, v: ControllerVariables, v_prime: ControllerVariables, message_ops: MessageOps) -> bool {
    message_ops.recv.is_Some()
    && match message_ops.recv.get_Some_0() {
        Message::APIOpResponse(api_op_response) => {
            match v.pending_api_op_request {
                Option::Some(api_op_request) => 
                    all_well_formed(c, v, v_prime, message_ops)
                    && v === ControllerVariables{
                                last_api_op_response: v.last_api_op_response,
                                pending_api_op_request: v.pending_api_op_request,
                                state_cache: v.state_cache,
                                before_receiving_response: v.before_receiving_response,
                                ..v_prime
                             }
                    && v.in_reconcile
                    && v.before_receiving_response
                    && !v_prime.before_receiving_response
                    && v.triggering_key.is_Some()
                    && v_prime.last_api_op_response === Option::Some(api_op_response)
                    && v_prime.pending_api_op_request.is_None()
                    && message_ops.send.is_None()
                    // response and request need to match
                    && api_op_response.api_op_request === api_op_request
                    // if success, update the cache; otherwise do nothing
                    && if api_op_response.success {
                        state_transition_by_api_op(v.state_cache, v_prime.state_cache, api_op_response.api_op_request.api_op)
                    } else {
                        v.state_cache === v_prime.state_cache
                    },
                Option::None => false,
            }
        }
        _ => false,
    }
}

/// end_reconcile does the following
/// - Set in_reconcile to false, which means reconcile is finished and the controller can receive notifications now
pub open spec fn end_reconcile(c: ControllerConstants, v: ControllerVariables, v_prime: ControllerVariables, message_ops: MessageOps) -> bool {
    all_well_formed(c, v, v_prime, message_ops)
    && v === ControllerVariables{
                triggering_key: v.triggering_key,
                in_reconcile: v.in_reconcile,
                reconcile_step: v.reconcile_step,
                last_api_op_response: v.last_api_op_response,
                state_cache: v.state_cache,
                ..v_prime
             }
    && v.in_reconcile
    && !v.before_receiving_response
    && v.triggering_key.is_Some()
    && v_prime.triggering_key.is_None()
    && v.pending_api_op_request.is_None()
    && !v_prime.in_reconcile
    && v_prime.last_api_op_response.is_None()
    && ((v.reconcile_step === ReconcileStep::Done) || (v.reconcile_step === ReconcileStep::Retry))
    && v_prime.reconcile_step === ReconcileStep::Init
    && v_prime.state_cache.empty()
    && message_ops.recv.is_None()
    && message_ops.send.is_None()
    // TODO: end_reconcile should differentiate Done and Retry
}

pub open spec fn next_step(c: ControllerConstants, v: ControllerVariables, v_prime: ControllerVariables, message_ops: MessageOps, step: ControllerStep) -> bool {
    match step {
        ControllerStep::ReceiveInformerUpdateStep => receive_api_watch_notification(c, v, v_prime, message_ops),
        ControllerStep::StartReconcileStep => start_reconcile(c, v, v_prime, message_ops),
        ControllerStep::ContinueReconcileStep => continue_reconcile(c, v, v_prime, message_ops),
        ControllerStep::ReceiveAPIOpResponseStep => receive_api_op_response(c, v, v_prime, message_ops),
        ControllerStep::EndReconcileStep => end_reconcile(c, v, v_prime, message_ops),
    }
}

pub open spec fn next(c: ControllerConstants, v: ControllerVariables, v_prime: ControllerVariables, message_ops: MessageOps) -> bool {
    exists |step: ControllerStep| next_step(c, v, v_prime, message_ops, step)
}

}
