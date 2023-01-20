// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::state_machine::action::*;
use crate::kubernetes_cluster::spec::common::*;
use crate::pervasive::{option::*, seq::*, set::*};
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct ClientState {}

pub struct ClientActionInput {
    pub recv: Option<Message>,
    pub cr: ResourceObj,
}

pub enum Step {
    SendCreateCR,
    SendDeleteCR,
}

pub type ClientStateMachine = StateMachine<ClientState, ClientActionInput, ClientActionInput, Set<Message>, Step>;

pub type ClientAction = Action<ClientState, ClientActionInput, Set<Message>>;

pub type ClientActionResult = ActionResult<ClientState, Set<Message>>;

pub open spec fn msg_to_kubernetes_api(msg_content: MessageContent) -> Message {
    form_msg(HostId::Client, HostId::KubernetesAPI, msg_content)
}

pub open spec fn send_create_cr() -> ClientAction {
    Action {
        precondition: |input: ClientActionInput, s| {
            &&& input.cr.key.kind.is_CustomResourceKind()
            &&& input.recv.is_None()
        },
        transition: |input: ClientActionInput, s| {
            (s, set![msg_to_kubernetes_api(create_req_msg(ResourceObj{key: input.cr.key}))])
        },
    }
}

pub open spec fn send_delete_cr() -> ClientAction {
    Action {
        precondition: |input: ClientActionInput, s| {
            &&& input.cr.key.kind.is_CustomResourceKind()
            &&& input.recv.is_None()
        },
        transition: |input: ClientActionInput, s| {
            (s, set![msg_to_kubernetes_api(delete_req_msg(input.cr.key))])
        },
    }
}

pub open spec fn client() -> ClientStateMachine {
    StateMachine {
        init: |s: ClientState| true,
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
