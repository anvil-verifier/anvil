// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster_v2::spec::{controller::types::*, message::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub open spec fn run_scheduled_reconcile(model: ReconcileModel) -> ControllerAction {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState| {
            &&& input.scheduled_cr_key.is_Some()
            &&& input.scheduled_cr_key.get_Some_0().kind == model.kind
            &&& s.scheduled_reconciles.contains_key(input.scheduled_cr_key.get_Some_0())
            &&& input.recv.is_None()
            &&& !s.ongoing_reconciles.contains_key(input.scheduled_cr_key.get_Some_0())
        },
        transition: |input: ControllerActionInput, s: ControllerState| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let initialized_ongoing_reconcile = OngoingReconcile {
                triggering_cr: s.scheduled_reconciles[cr_key],
                pending_req_msg: None,
                local_state: (model.init)(),
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

pub open spec fn continue_reconcile(model: ReconcileModel, controller_id: int) -> ControllerAction {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState| {
            if input.scheduled_cr_key.is_Some() {
                let cr_key = input.scheduled_cr_key.get_Some_0();

                &&& cr_key.kind == model.kind
                &&& s.ongoing_reconciles.contains_key(cr_key)
                &&& !(model.done)(s.ongoing_reconciles[cr_key].local_state)
                &&& !(model.error)(s.ongoing_reconciles[cr_key].local_state)
                &&& if s.ongoing_reconciles[cr_key].pending_req_msg.is_Some() {
                    &&& input.recv.is_Some()
                    &&& (input.recv.get_Some_0().content.is_APIResponse() || input.recv.get_Some_0().content.is_ExternalResponse())
                    &&& Message::resp_msg_matches_req_msg(input.recv.get_Some_0(), s.ongoing_reconciles[cr_key].pending_req_msg.get_Some_0())
                } else {
                    input.recv.is_None()
                }
            } else {
                false
            }
        },
        transition: |input: ControllerActionInput, s: ControllerState| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let reconcile_state = s.ongoing_reconciles[cr_key];
            let resp_o = if input.recv.is_Some() {
                if input.recv.get_Some_0().content.is_APIResponse() {
                    Some(ResponseContent::KubernetesResponse(input.recv.get_Some_0().content.get_APIResponse_0()))
                } else {
                    Some(ResponseContent::ExternalResponse(input.recv.get_Some_0().content.get_ExternalResponse_0()))
                }
            } else {
                None
            };
            let (local_state_prime, req_o) = (model.transition)(reconcile_state.triggering_cr, resp_o, reconcile_state.local_state);
            let (pending_req_msg, send, rest_id_allocator_prime) = if req_o.is_Some() {
                let pending_req_msg = match req_o.get_Some_0() {
                    RequestContent::KubernetesRequest(req) => {
                        Some(Message::controller_req_msg(controller_id, input.rest_id_allocator.allocate().1, req))
                    },
                    RequestContent::ExternalRequest(req) => {
                        Some(Message::controller_external_req_msg(controller_id, input.rest_id_allocator.allocate().1, req))
                    }
                };
                (pending_req_msg, Multiset::singleton(pending_req_msg.get_Some_0()), input.rest_id_allocator.allocate().0)
            } else {
                (None, Multiset::empty(), input.rest_id_allocator)
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
                send: send,
                rest_id_allocator: rest_id_allocator_prime,
            };
            (s_prime, output)
        }
    }
}

pub open spec fn end_reconcile(model: ReconcileModel) -> ControllerAction {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState| {
            if input.scheduled_cr_key.is_Some() {
                let cr_key = input.scheduled_cr_key.get_Some_0();

                &&& cr_key.kind == model.kind
                &&& s.ongoing_reconciles.contains_key(cr_key)
                &&& (model.done)(s.ongoing_reconciles[cr_key].local_state) || (model.error)(s.ongoing_reconciles[cr_key].local_state)
                &&& input.recv.is_None()
            } else {
                false
            }
        },
        transition: |input: ControllerActionInput, s: ControllerState| {
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

pub open spec fn init_controller_state() -> ControllerState {
    ControllerState {
        ongoing_reconciles: Map::<ObjectRef, OngoingReconcile>::empty(),
        scheduled_reconciles: Map::<ObjectRef, DynamicObjectView>::empty(),
    }
}

pub open spec fn controller(model: ReconcileModel, controller_id: int) -> ControllerStateMachine {
    StateMachine {
        init: |s: ControllerState| {
            s == init_controller_state()
        },
        actions: set![
            run_scheduled_reconcile(model),
            continue_reconcile(model, controller_id),
            end_reconcile(model)
        ],
        step_to_action: |step: ControllerStep| {
            match step {
                ControllerStep::RunScheduledReconcile => run_scheduled_reconcile(model),
                ControllerStep::ContinueReconcile => continue_reconcile(model, controller_id),
                ControllerStep::EndReconcile => end_reconcile(model),
            }
        },
        action_input: |step: ControllerStep, input: ControllerActionInput| {
            input
        }
    }
}

}
