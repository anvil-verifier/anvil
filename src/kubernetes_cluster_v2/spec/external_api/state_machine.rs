// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster_v2::spec::{external_api::types::*, message::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub open spec fn handle_external_request() -> ExternalAPIAction {
    Action {
        precondition: |input: ExternalAPIActionInput, s: ExternalAPIState| {
            &&& input.recv.is_Some()
            &&& input.recv.get_Some_0().content.is_ExternalRequest()
        },
        transition: |input: ExternalAPIActionInput, s: ExternalAPIState| {
            let req_msg = input.recv.get_Some_0();
            let resources = input.resources;
            let (inner_s_prime, resp) = (s.transition)(req_msg.content.get_ExternalRequest_0(), s.state, resources);
            let s_prime = ExternalAPIState {
                state: inner_s_prime,
                ..s
            };
            let resp_msg = Message::form_external_resp_msg(req_msg, resp);
            (s_prime, ExternalAPIActionOutput {
                send: Multiset::singleton(resp_msg),
            })
        },
    }
}

pub open spec fn external_api(init_state: ExternalAPIState) -> ExternalAPIStateMachine {
    StateMachine {
        init: |s: ExternalAPIState| {
            s == init_state
        },
        actions: set![handle_external_request()],
        step_to_action: |step: ExternalAPIStep| {
            match step {
                ExternalAPIStep::HandleExternalRequest => handle_external_request(),
            }
        },
        action_input: |step: ExternalAPIStep, input: ExternalAPIActionInput| {
            input
        }
    }
}

}
