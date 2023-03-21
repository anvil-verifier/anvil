// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{common::*, object::*};
use crate::kubernetes_cluster::spec::{controller::common::*, message::*, reconciler::*};
use crate::pervasive::{map::*, multiset::*, option::*, seq::*, set::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn run_scheduled_reconcile<T>(reconciler: Reconciler<T>) -> ControllerAction<T> {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState<T>| {
            &&& input.scheduled_cr_key.is_Some()
            &&& s.scheduled_reconciles.contains(input.scheduled_cr_key.get_Some_0())
            &&& input.recv.is_None()
            &&& !s.ongoing_reconciles.dom().contains(input.scheduled_cr_key.get_Some_0())
        },
        transition: |input: ControllerActionInput, s: ControllerState<T>| {
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
            let send = Multiset::empty();
            (s_prime, send)
        },
    }
}

pub open spec fn continue_reconcile<T>(reconciler: Reconciler<T>) -> ControllerAction<T> {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState<T>| {
            if input.scheduled_cr_key.is_Some() {
                let cr_key = input.scheduled_cr_key.get_Some_0();

                &&& s.ongoing_reconciles.dom().contains(cr_key)
                &&& !(reconciler.reconcile_done)(s.ongoing_reconciles[cr_key].local_state)
                &&& !(reconciler.reconcile_error)(s.ongoing_reconciles[cr_key].local_state)
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
        transition: |input: ControllerActionInput, s: ControllerState<T>| {
            let resp_o = if input.recv.is_Some() {
                Option::Some(input.recv.get_Some_0().content.get_APIResponse_0())
            } else {
                Option::None
            };
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let reconcile_state = s.ongoing_reconciles[cr_key];

            let (local_state_prime, req_o) = (reconciler.reconcile_core)(cr_key, resp_o, reconcile_state.local_state);

            let pending_req_msg = if req_o.is_Some() {
                Option::Some(controller_req_msg(req_o.get_Some_0(), s.req_id))
            } else {
                Option::None
            };

            let reconcile_state_prime = OngoingReconcile {
                pending_req_msg: pending_req_msg,
                local_state: local_state_prime,
            };
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, reconcile_state_prime),
                req_id: s.req_id + 1,
                ..s
            };
            let send = if pending_req_msg.is_Some() {
                Multiset::singleton(pending_req_msg.get_Some_0())
            } else {
                Multiset::empty()
            };
            (s_prime, send)
        }
    }
}

pub open spec fn end_reconcile<T>(reconciler: Reconciler<T>) -> ControllerAction<T> {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState<T>| {
            if input.scheduled_cr_key.is_Some() {
                let cr_key = input.scheduled_cr_key.get_Some_0();

                &&& s.ongoing_reconciles.dom().contains(cr_key)
                &&& ((reconciler.reconcile_done)(s.ongoing_reconciles[cr_key].local_state) || (reconciler.reconcile_error)(s.ongoing_reconciles[cr_key].local_state))
                &&& input.recv.is_None()
            } else {
                false
            }
        },
        transition: |input: ControllerActionInput, s: ControllerState<T>| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.remove(cr_key),
                ..s
            };
            (s_prime, Multiset::empty())
        }
    }
}

}
