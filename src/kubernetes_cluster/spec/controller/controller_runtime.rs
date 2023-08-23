// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::spec::{cluster::Cluster, controller::common::*, message::*};
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn run_scheduled_reconcile() -> ControllerAction<K, E, R> {
    Action {
        precondition: |input: ControllerActionInput<E>, s: ControllerState<K, E, R>| {
            &&& input.scheduled_cr_key.is_Some()
            &&& input.scheduled_cr_key.get_Some_0().kind == K::kind()
            &&& s.scheduled_reconciles.contains_key(input.scheduled_cr_key.get_Some_0())
            &&& input.recv.is_None()
            &&& !s.ongoing_reconciles.dom().contains(input.scheduled_cr_key.get_Some_0())
        },
        transition: |input: ControllerActionInput<E>, s: ControllerState<K, E, R>| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let initialized_ongoing_reconcile = OngoingReconcile {
                triggering_cr: s.scheduled_reconciles[cr_key],
                pending_req_msg: None,
                local_state: R::reconcile_init_state(),
            };
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, initialized_ongoing_reconcile),
                scheduled_reconciles: s.scheduled_reconciles.remove(cr_key),
                ..s
            };
            let output = ControllerActionOutput {
                send: Multiset::empty(),
                rest_id_allocator: input.rest_id_allocator,
            };
            (s_prime, output)
        },
    }
}

pub open spec fn continue_reconcile() -> ControllerAction<K, E, R> {
    Action {
        precondition: |input: ControllerActionInput<E>, s: ControllerState<K, E, R>| {
            if input.scheduled_cr_key.is_Some() {
                let cr_key = input.scheduled_cr_key.get_Some_0();

                &&& cr_key.kind == K::kind()
                &&& s.ongoing_reconciles.dom().contains(cr_key)
                &&& !R::reconcile_done(s.ongoing_reconciles[cr_key].local_state)
                &&& !R::reconcile_error(s.ongoing_reconciles[cr_key].local_state)
                // Split cases:
                // (1) there is a pending request which is destined for kubernetes/external api;
                // (2) there is no pending request or external api input;

                &&& if s.ongoing_reconciles[cr_key].pending_req_msg.is_Some() {
                    &&& input.recv.is_Some()
                    &&& input.recv.get_Some_0().content.is_APIResponse()
                    &&& Message::resp_msg_matches_req_msg(input.recv.get_Some_0(), s.ongoing_reconciles[cr_key].pending_req_msg.get_Some_0())
                } else {
                    &&& input.recv.is_None()
                }
            } else {
                false
            }
        },
        transition: |input: ControllerActionInput<E>, s: ControllerState<K, E, R>| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let reconcile_state = s.ongoing_reconciles[cr_key];
            let resp_o = if input.recv.is_Some() {
                Some(ResponseView::KResponse(input.recv.get_Some_0().content.get_APIResponse_0()))
            } else {
                None
            };
            let (local_state_prime, req_o) = R::reconcile_core(reconcile_state.triggering_cr, resp_o, reconcile_state.local_state);
            if req_o.is_Some() {
                let rest_id_allocator_prime = input.rest_id_allocator.allocate().0;
                let pending_req_msg = match req_o.get_Some_0() {
                    RequestView::KRequest(req) => {
                        Some(Message::controller_req_msg(req, input.rest_id_allocator.allocate().1))
                    },
                    RequestView::ExternalRequest(req) => {
                        Some(Message::controller_external_req_msg(req, input.rest_id_allocator.allocate().1))
                    }
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
                let output = ControllerActionOutput {
                    send: Multiset::singleton(pending_req_msg.get_Some_0()),
                    rest_id_allocator: rest_id_allocator_prime,
                };
                (s_prime, output)
           } else {
                let reconcile_state_prime = OngoingReconcile {
                    pending_req_msg: None,
                    local_state: local_state_prime,
                    ..reconcile_state
                };
                let s_prime = ControllerState {
                    ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, reconcile_state_prime),
                    ..s
                };
                let output = ControllerActionOutput {
                    send: Multiset::empty(),
                    // TODO: we don't have to increment the rest id here
                    rest_id_allocator: input.rest_id_allocator.allocate().0,
                };
                (s_prime, output)
            }
        }
    }
}

pub open spec fn end_reconcile() -> ControllerAction<K, E, R> {
    Action {
        precondition: |input: ControllerActionInput<E>, s: ControllerState<K, E, R>| {
            if input.scheduled_cr_key.is_Some() {
                let cr_key = input.scheduled_cr_key.get_Some_0();

                &&& cr_key.kind == K::kind()
                &&& s.ongoing_reconciles.dom().contains(cr_key)
                &&& (R::reconcile_done(s.ongoing_reconciles[cr_key].local_state) || R::reconcile_error(s.ongoing_reconciles[cr_key].local_state))
                &&& input.recv.is_None()
            } else {
                false
            }
        },
        transition: |input: ControllerActionInput<E>, s: ControllerState<K, E, R>| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.remove(cr_key),
                ..s
            };
            let output = ControllerActionOutput {
                send: Multiset::empty(),
                rest_id_allocator: input.rest_id_allocator,
            };
            (s_prime, output)
        }
    }
}

}

}
