// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::resource::*;
use crate::kubernetes_cluster::spec::{cluster::Cluster, external_api::types::*, message::*};
use crate::pervasive_ext::string_view::*;
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn handle_external_request() -> ExternalAPIAction<E> {
    Action {
        precondition: |input: ExternalAPIActionInput<E>, s: ExternalAPIState<E>| {
            &&& input.recv.is_Some()
            &&& input.recv.get_Some_0().content.is_ExternalAPIRequest()
            // This dst check is redundant since the compound state machine has checked it
            &&& input.recv.get_Some_0().dst == HostId::ExternalAPI
        },
        transition: |input: ExternalAPIActionInput<E>, s: ExternalAPIState<E>| {
            let req_msg = input.recv.get_Some_0();
            let (inner_s_prime, resp_o) = E::transition(req_msg.content.get_ExternalAPIRequest_0(), s.state, input.resources);
            let s_prime = ExternalAPIState {
                state: inner_s_prime,
            };
            let send = if resp_o.is_None() {
                Multiset::empty()
            } else {
                let resp_msg = Message::form_external_resp_msg(req_msg, resp_o.get_Some_0());
                Multiset::singleton(resp_msg)
            };
            let output = ExternalAPIActionOutput {
                send: send,
            };
            (s_prime, output)
        },
    }
}

pub open spec fn external_api() -> ExternalAPIStateMachine<E> {
    StateMachine {
        init: |s: ExternalAPIState<E>| {
            s.state == E::init_state()
        },
        actions: set![Self::handle_external_request()],
        step_to_action: |step: ExternalAPIStep| {
            match step {
                ExternalAPIStep::HandleExternalRequest => Self::handle_external_request(),
            }
        },
        action_input: |step: ExternalAPIStep, input: ExternalAPIActionInput<E>| {
            input
        }
    }
}

}

}
