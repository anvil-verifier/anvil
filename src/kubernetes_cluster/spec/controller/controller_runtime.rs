// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::state_machine::action::*;
use crate::kubernetes_cluster::spec::{common::*, controller::common::*, reconciler::*};
use crate::pervasive::{map::*, option::*, seq::*, set::*};
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
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
            let initialized_ongoing_reconcile = OngoingReconcile {
                pending_req_msg: Option::None,
                local_state: (reconciler.reconcile_init_state)(),
            };
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, initialized_ongoing_reconcile),
                ..s
            };
            let send = Set::empty();
            (s_prime, send)
        },
    }
}

pub open spec fn run_scheduled_reconcile(reconciler: Reconciler) -> ControllerAction {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState| {
            &&& input.scheduled_cr_key.is_Some()
            &&& s.scheduled_reconciles.contains(input.scheduled_cr_key.get_Some_0())
            &&& input.recv.is_None()
            &&& !s.ongoing_reconciles.dom().contains(input.scheduled_cr_key.get_Some_0())
        },
        transition: |input: ControllerActionInput, s: ControllerState| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let initialized_ongoing_reconcile = OngoingReconcile {
                pending_req_msg: Option::None,
                local_state: (reconciler.reconcile_init_state)(),
            };
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, initialized_ongoing_reconcile),
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

                &&& s.ongoing_reconciles.dom().contains(cr_key)
                &&& !(reconciler.reconcile_done)(s.ongoing_reconciles[cr_key].local_state)
                &&& if input.recv.is_Some() {
                    &&& input.recv.get_Some_0().content.is_APIResponse()
                    &&& s.ongoing_reconciles[cr_key].pending_req_msg.is_Some()
                    &&& resp_msg_matches_req_msg(input.recv.get_Some_0(), s.ongoing_reconciles[cr_key].pending_req_msg.get_Some_0())
                } else {
                    s.ongoing_reconciles[cr_key].pending_req_msg.is_None()
                }
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

            let (local_state_prime, req_o) = (reconciler.reconcile_core)(cr_key, resp_o, reconcile_state.local_state);

            let pending_req_msg = if req_o.is_Some() {
                Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(req_o.get_Some_0())))
            } else {
                Option::None
            };

            let reconcile_state_prime = OngoingReconcile {
                pending_req_msg: pending_req_msg,
                local_state: local_state_prime,
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

pub open spec fn end_reconcile(reconciler: Reconciler) -> ControllerAction {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState| {
            if input.scheduled_cr_key.is_Some() {
                let cr_key = input.scheduled_cr_key.get_Some_0();

                &&& s.ongoing_reconciles.dom().contains(cr_key)
                &&& (reconciler.reconcile_done)(s.ongoing_reconciles[cr_key].local_state)
                &&& input.recv.is_None()
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
