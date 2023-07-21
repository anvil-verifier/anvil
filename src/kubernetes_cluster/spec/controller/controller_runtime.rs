// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::spec::{controller::common::*, message::*};
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub open spec fn run_scheduled_reconcile<K: ResourceView, R: Reconciler<K>>() -> ControllerAction<K, R> {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState<K, R>| {
            &&& input.scheduled_cr_key.is_Some()
            &&& input.scheduled_cr_key.get_Some_0().kind == K::kind()
            &&& s.scheduled_reconciles.contains_key(input.scheduled_cr_key.get_Some_0())
            &&& input.recv.is_None()
            &&& !s.ongoing_reconciles.dom().contains(input.scheduled_cr_key.get_Some_0())
        },
        transition: |input: ControllerActionInput, s: ControllerState<K, R>| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let initialized_ongoing_reconcile = OngoingReconcile {
                triggering_cr: s.scheduled_reconciles[cr_key],
                pending_req_msg: Option::None,
                pending_lib_req: Option::None,
                lib_response: Option::None,
                local_state: R::reconcile_init_state(),
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

pub open spec fn continue_reconcile<K: ResourceView, R: Reconciler<K>>() -> ControllerAction<K, R> {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState<K, R>| {
            if input.scheduled_cr_key.is_Some() {
                let cr_key = input.scheduled_cr_key.get_Some_0();

                &&& cr_key.kind == K::kind()
                &&& s.ongoing_reconciles.dom().contains(cr_key)
                &&& !R::reconcile_done(s.ongoing_reconciles[cr_key].local_state)
                &&& !R::reconcile_error(s.ongoing_reconciles[cr_key].local_state)
                // Split cases:
                // (1) there is a pending request which is destined for kubernetes api;
                // (2) there is a pending request which is destined for external library and no response;
                // (3) there is a pending request which is destined for external library and a corresponding response;
                // (4) there is no pending request;
                // The four cases don't overlap each other, and we must make them mutually exclusive in the 
                // precondition, i.e., there should not be a state which satifies the precondition but fits for more
                // than one case of the four.
                // Note that if there is no pending request destined for kubernetes api, we have to require that
                // the recv field of input is empty and exclude the case where pending_lib_req is empty and 
                // lib_response is not.
                &&& if s.ongoing_reconciles[cr_key].pending_req_msg.is_Some() {
                    &&& s.ongoing_reconciles[cr_key].lib_response.is_None() // The response from external library should have been consumed if ever exists
                    &&& s.ongoing_reconciles[cr_key].pending_lib_req.is_None()
                    &&& input.recv.is_Some()
                    &&& input.recv.get_Some_0().content.is_APIResponse()
                    &&& resp_msg_matches_req_msg(input.recv.get_Some_0(), s.ongoing_reconciles[cr_key].pending_req_msg.get_Some_0())
                } else {
                    // We should not get response from other part of the GSM for this case.
                    &&& input.recv.is_None()
                    &&& if s.ongoing_reconciles[cr_key].pending_lib_req.is_None() {
                            s.ongoing_reconciles[cr_key].lib_response.is_None()
                        } else {
                            true
                        }
                }
            } else {
                false
            }
        },
        transition: |input: ControllerActionInput, s: ControllerState<K, R>| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let reconcile_state = s.ongoing_reconciles[cr_key];
            let resp_o = if input.recv.is_Some() {
                Option::Some(ResponseView::KResponse(input.recv.get_Some_0().content.get_APIResponse_0()))
            } else if reconcile_state.lib_response.is_Some() {
                Option::Some(ResponseView::ExternalResponse(reconcile_state.lib_response.get_Some_0()))
            } else {
                Option::None
            };
            if reconcile_state.pending_lib_req.is_Some() && reconcile_state.lib_response.is_None() {
                // This is the only case we should call the external Library.
                // We first make it do nothing here.
                let reconcile_state_prime = OngoingReconcile {
                    pending_lib_req: Option::None,
                    lib_response: Option::None, // Should be updated
                    ..reconcile_state
                };
                let s_prime = ControllerState {
                    ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, reconcile_state_prime),
                    ..s
                };
                (s_prime, (Multiset::empty(), input.rest_id_allocator.allocate().0))
            } else {
                // Otherwise, we call the reconcile_core.
                let (local_state_prime, req_o) = R::reconcile_core(reconcile_state.triggering_cr, resp_o, reconcile_state.local_state);
                if req_o.is_Some() {
                    match req_o.get_Some_0() {
                        RequestView::KRequest(req) => {
                            let (rest_id_allocator_prime, pending_req_msg) 
                                = (input.rest_id_allocator.allocate().0, Option::Some(controller_req_msg(req, input.rest_id_allocator.allocate().1)));
                            let reconcile_state_prime = OngoingReconcile {
                                pending_req_msg: pending_req_msg,
                                pending_lib_req: Option::None,
                                lib_response: Option::None,
                                local_state: local_state_prime,
                                ..reconcile_state
                            };
                            let s_prime = ControllerState {
                                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, reconcile_state_prime),
                                ..s
                            };
                            (s_prime, (Multiset::singleton(pending_req_msg.get_Some_0()), rest_id_allocator_prime))
                        },
                        RequestView::ExternalRequest(req) => {
                            let reconcile_state_prime = OngoingReconcile {
                                pending_req_msg: Option::None,
                                pending_lib_req: Option::Some(req),
                                lib_response: Option::None,
                                local_state: local_state_prime,
                                ..reconcile_state
                            };
                            let s_prime = ControllerState {
                                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, reconcile_state_prime),
                                ..s
                            };
                            (s_prime, (Multiset::empty(), input.rest_id_allocator.allocate().0))
                        }
                    }
                } else {
                    let reconcile_state_prime = OngoingReconcile {
                        pending_req_msg: Option::None,
                        pending_lib_req: Option::None,
                        lib_response: Option::None,
                        local_state: local_state_prime,
                        ..reconcile_state
                    };
                    let s_prime = ControllerState {
                        ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, reconcile_state_prime),
                        ..s
                    };
                    (s_prime, (Multiset::empty(), input.rest_id_allocator.allocate().0))
                }
            }
        }
    }
}

pub open spec fn end_reconcile<K: ResourceView, R: Reconciler<K>>() -> ControllerAction<K, R> {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState<K, R>| {
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
        transition: |input: ControllerActionInput, s: ControllerState<K, R>| {
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
