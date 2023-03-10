// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{custom_resource::*, object::*};
use crate::kubernetes_cluster::spec::common::*;
use crate::pervasive::{multiset::*, option::*, seq::*, set::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct ClientState {
    pub req_id: nat
}

pub struct ClientActionInput {
    pub recv: Option<Message>,
    pub cr: CustomResourceView,
}

pub enum Step {
    SendCreateCR,
    SendDeleteCR,
}

pub type ClientStateMachine = StateMachine<ClientState, ClientActionInput, ClientActionInput, Multiset<Message>, Step>;

pub type ClientAction = Action<ClientState, ClientActionInput, Multiset<Message>>;

pub type ClientActionResult = ActionResult<ClientState, Multiset<Message>>;

pub open spec fn client_req_msg(msg_content: MessageContent) -> Message {
    form_msg(HostId::Client, HostId::KubernetesAPI, msg_content)
}

pub open spec fn send_create_cr() -> ClientAction {
    Action {
        precondition: |input: ClientActionInput, s: ClientState| {
            &&& input.recv.is_None()
        },
        transition: |input: ClientActionInput, s: ClientState| {
            (ClientState {req_id: s.req_id + 1}, Multiset::singleton(client_req_msg(create_req_msg_content(KubernetesObject::CustomResource(input.cr), s.req_id))))
        },
    }
}

pub open spec fn send_delete_cr() -> ClientAction {
    Action {
        precondition: |input: ClientActionInput, s: ClientState| {
            &&& input.recv.is_None()
        },
        transition: |input: ClientActionInput, s: ClientState| {
            (ClientState {req_id: s.req_id + 1}, Multiset::singleton(client_req_msg(delete_req_msg_content(input.cr.object_ref(), s.req_id))))
        },
    }
}

pub open spec fn client() -> ClientStateMachine {
    StateMachine {
        init: |s: ClientState| {
            s == ClientState {
                req_id: 0,
            }
        },
        actions: set![send_create_cr(), send_delete_cr()],
        step_to_action: |step: Step| {
            match step {
                Step::SendCreateCR => send_create_cr(),
                Step::SendDeleteCR => send_delete_cr(),
            }
        },
        action_input: |step: Step, input: ClientActionInput| {
            input
        }
    }
}

}
