// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::spec::{controller::common::*, message::*};
use crate::reconciler::spec::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub open spec fn run_scheduled_reconcile<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>() -> ControllerAction<K, T> {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState<K, T>| {
            &&& input.scheduled_cr_key.is_Some()
            &&& input.scheduled_cr_key.get_Some_0().kind == K::kind()
            &&& s.scheduled_reconciles.contains_key(input.scheduled_cr_key.get_Some_0())
            &&& input.recv.is_None()
            &&& !s.ongoing_reconciles.dom().contains(input.scheduled_cr_key.get_Some_0())
        },
        transition: |input: ControllerActionInput, s: ControllerState<K, T>| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let initialized_ongoing_reconcile = OngoingReconcile {
                triggering_cr: s.scheduled_reconciles[cr_key],
                pending_req_msg: Option::None,
                local_state: ReconcilerType::reconcile_init_state(),
            };
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, initialized_ongoing_reconcile),
                scheduled_reconciles: s.scheduled_reconciles.remove(cr_key),
                ..s
            };
            let send = Multiset::empty();
            (s_prime, (send, input.rest_id_allocator))
        },
    }
}

pub open spec fn continue_reconcile<K: ResourceView, T, ReconcilerType: Reconciler<K ,T>>() -> ControllerAction<K, T> {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState<K, T>| {
            if input.scheduled_cr_key.is_Some() {
                let cr_key = input.scheduled_cr_key.get_Some_0();

                &&& cr_key.kind == K::kind()
                &&& s.ongoing_reconciles.dom().contains(cr_key)
                &&& !ReconcilerType::reconcile_done(s.ongoing_reconciles[cr_key].local_state)
                &&& !ReconcilerType::reconcile_error(s.ongoing_reconciles[cr_key].local_state)
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
        transition: |input: ControllerActionInput, s: ControllerState<K, T>| {
            let resp_o = if input.recv.is_Some() {
                Option::Some(ResponseView::KubernetesAPI(input.recv.get_Some_0().content.get_APIResponse_0()))
            } else {
                Option::None
            };
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let reconcile_state = s.ongoing_reconciles[cr_key];

            let (local_state_prime, req_o) = ReconcilerType::reconcile_core(reconcile_state.triggering_cr, resp_o, reconcile_state.local_state);

            let (rest_id_allocator_prime, pending_req_msg) = if req_o.is_Some() && req_o.get_Some_0().is_KubernetesAPI() {
                (
                    input.rest_id_allocator.allocate().0,
                    Option::Some(controller_req_msg(req_o.get_Some_0().get_KubernetesAPI_0(), input.rest_id_allocator.allocate().1))
                )
            } else {
                (input.rest_id_allocator, Option::None)
            };

            let reconcile_state_prime = OngoingReconcile {
                pending_req_msg: pending_req_msg,
                local_state: local_state_prime,
                ..reconcile_state
            };
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, reconcile_state_prime),
                ..s
            };
            let send = if pending_req_msg.is_Some() {
                Multiset::singleton(pending_req_msg.get_Some_0())
            } else {
                Multiset::empty()
            };
            (s_prime, (send, rest_id_allocator_prime))
        }
    }
}

pub open spec fn end_reconcile<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>() -> ControllerAction<K, T> {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState<K, T>| {
            if input.scheduled_cr_key.is_Some() {
                let cr_key = input.scheduled_cr_key.get_Some_0();

                &&& cr_key.kind == K::kind()
                &&& s.ongoing_reconciles.dom().contains(cr_key)
                &&& (ReconcilerType::reconcile_done(s.ongoing_reconciles[cr_key].local_state) || ReconcilerType::reconcile_error(s.ongoing_reconciles[cr_key].local_state))
                &&& input.recv.is_None()
            } else {
                false
            }
        },
        transition: |input: ControllerActionInput, s: ControllerState<K, T>| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.remove(cr_key),
                ..s
            };
            (s_prime, (Multiset::empty(), input.rest_id_allocator))
        }
    }
}

}
