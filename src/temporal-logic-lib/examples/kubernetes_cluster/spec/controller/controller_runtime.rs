// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::kubernetes_cluster::spec::{common::*, controller::common::*};
use crate::pervasive::{map::*, option::*, seq::*, set::*};
use crate::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

/// This action specifies how the watcher triggers reconcile.
/// It is highly simplified compared to the actual watcher implementation in kube-rs:
/// (1) The triggering condition should come from the developer. Currently we hardcode it in
/// reconcile_trigger.
/// (2) The watcher and reconciler run concurrently: the watcher can take incoming events while
/// the reconciler is in reconcile. If the reconciler is working on object X, all the incoming
/// events related to X will stay pending in a queue.
/// (3) The watcher deduplicates triggering events for the same object: if an event for object X
/// comes but there is already another pending event for the same object, the incoming event is
/// discarded.
pub open spec fn trigger_reconcile(reconciler: Reconciler) -> ControllerAction {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState| {
            // TODO: we should have an action for requeued reconcile
            // TODO: We should have multiple queues for storing triggering events.
            // Each queue stores the event relates to the same cr key.
            &&& input.scheduled_cr_key.is_None()
            &&& input.recv.is_Some()
            &&& input.recv.get_Some_0().dst === HostId::CustomController
            &&& input.recv.get_Some_0().content.is_WatchEvent()
            &&& (reconciler.reconcile_trigger)(input.recv.get_Some_0()).is_Some()
            &&& !s.ongoing_reconciles.dom().contains((reconciler.reconcile_trigger)(input.recv.get_Some_0()).get_Some_0())
        },
        transition: |input: ControllerActionInput, s: ControllerState| {
            let cr_key = (reconciler.reconcile_trigger)(input.recv.get_Some_0()).get_Some_0();
            let initialized_reconcile_state = ReconcileState {
                reconcile_step: ReconcileCoreStep::Init,
                pending_req_msg: Option::None,
            };
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, initialized_reconcile_state),
                ..s
            };
            let send = Set::empty();
            (s_prime, send)
        },
    }
}

pub open spec fn run_scheduled_reconcile() -> ControllerAction {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState| {
            &&& input.scheduled_cr_key.is_Some()
            &&& s.scheduled_reconciles.contains(input.scheduled_cr_key.get_Some_0())
            &&& input.recv.is_None()
            &&& !s.ongoing_reconciles.dom().contains(input.scheduled_cr_key.get_Some_0())
        },
        transition: |input: ControllerActionInput, s: ControllerState| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let initialized_reconcile_state = ReconcileState {
                reconcile_step: ReconcileCoreStep::Init,
                pending_req_msg: Option::None,
            };
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, initialized_reconcile_state),
                scheduled_reconciles: s.scheduled_reconciles.remove(cr_key),
                ..s
            };
            let send = Set::empty();
            (s_prime, send)
        },
    }
}

pub open spec fn continue_reconcile(reconciler: Reconciler) -> ControllerAction {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState| {
            if input.scheduled_cr_key.is_Some() {
                let cr_key = input.scheduled_cr_key.get_Some_0();
                let reconcile_state = s.ongoing_reconciles[cr_key];

                &&& s.ongoing_reconciles.dom().contains(cr_key)
                &&& if input.recv.is_Some() {
                    &&& input.recv.get_Some_0().content.is_APIResponse()
                    &&& reconcile_state.pending_req_msg.is_Some()
                    &&& resp_msg_matches_req_msg(input.recv.get_Some_0(), reconcile_state.pending_req_msg.get_Some_0())
                } else {
                    reconcile_state.pending_req_msg.is_None()
                }
                &&& !ending_step(reconcile_state.reconcile_step)
            } else {
                false
            }
        },
        transition: |input: ControllerActionInput, s: ControllerState| {
            let resp_o = if input.recv.is_Some() {
                Option::Some(input.recv.get_Some_0().content.get_APIResponse_0())
            } else {
                Option::None
            };
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let reconcile_state = s.ongoing_reconciles[cr_key];

            let (next_step, req_o) = (reconciler.reconcile_core)(cr_key, reconcile_state.reconcile_step, resp_o);

            let pending_req_msg = if req_o.is_Some() {
                Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(req_o.get_Some_0())))
            } else {
                Option::None
            };
            let reconcile_state_prime = ReconcileState {
                reconcile_step: next_step,
                pending_req_msg: pending_req_msg,
            };
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, reconcile_state_prime),
                ..s
            };
            let send = if pending_req_msg.is_Some() {
                set![pending_req_msg.get_Some_0()]
            } else {
                Set::empty()
            };
            (s_prime, send)
        }
    }
}

pub open spec fn end_reconcile() -> ControllerAction {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState| {
            if input.scheduled_cr_key.is_Some() {
                let cr_key = input.scheduled_cr_key.get_Some_0();
                let reconcile_state = s.ongoing_reconciles[cr_key];

                &&& s.ongoing_reconciles.dom().contains(cr_key)
                &&& input.recv.is_None()
                &&& ending_step(reconcile_state.reconcile_step)
            } else {
                false
            }
        },
        transition: |input: ControllerActionInput, s: ControllerState| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.remove(cr_key),
                scheduled_reconciles: s.scheduled_reconciles.insert(cr_key),
                ..s
            };
            (s_prime, Set::empty())
        }
    }
}

}
