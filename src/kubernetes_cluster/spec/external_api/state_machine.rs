// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::Cluster, external_api::types::*, message::*};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::{multiset::*, prelude::*};

verus! {

impl <K: CustomResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn handle_external_request_helper(req_msg: MsgType<E>, s: ExternalAPIState<E>, resources: StoredState) -> (ExternalAPIState<E>, MsgType<E>) {
    let (inner_s_prime, resp) = E::transition(req_msg.content.get_ExternalAPIRequest_0(), resources, s.state);
    let s_prime = ExternalAPIState {
        state: inner_s_prime,
    };
    let resp_msg = Message::form_external_resp_msg(req_msg, resp);
    (s_prime, resp_msg)
}

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
            let (s_prime, resp_msg) = Self::handle_external_request_helper(req_msg, s, input.resources);
            (s_prime, ExternalAPIActionOutput {
                send: Multiset::singleton(resp_msg),
            })
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
