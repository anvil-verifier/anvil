// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{custom_resource::*, dynamic::*};
use crate::kubernetes_cluster::spec::{channel::*, message::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;
use vstd::{multiset::*, option::*, seq::*, set::*};

verus! {

pub struct ClientState {}

pub enum Step {
    SendCreateCR,
    SendDeleteCR,
}

pub struct ClientActionInput {
    pub recv: Option<Message>,
    pub cr: CustomResourceView,
    pub chan_manager: ChannelManager,
}

pub type ClientActionOutput = (Multiset<Message>, ChannelManager);

pub type ClientStateMachine = StateMachine<ClientState, ClientActionInput, ClientActionInput, ClientActionOutput, Step>;

pub type ClientAction = Action<ClientState, ClientActionInput, ClientActionOutput>;

pub open spec fn client_req_msg(msg_content: MessageContent) -> Message {
    form_msg(HostId::Client, HostId::KubernetesAPI, msg_content)
}

pub open spec fn send_create_cr() -> ClientAction {
    Action {
        precondition: |input: ClientActionInput, s: ClientState| {
            &&& input.recv.is_None()
        },
        transition: |input: ClientActionInput, s: ClientState| {
            (ClientState{}, (Multiset::singleton(client_req_msg(create_req_msg_content(input.cr.to_dynamic_object(), input.chan_manager.allocate().1))), input.chan_manager.allocate().0))
        },
    }
}

pub open spec fn send_delete_cr() -> ClientAction {
    Action {
        precondition: |input: ClientActionInput, s: ClientState| {
            &&& input.recv.is_None()
        },
        transition: |input: ClientActionInput, s: ClientState| {
            (ClientState{}, (Multiset::singleton(client_req_msg(delete_req_msg_content(input.cr.object_ref(), input.chan_manager.allocate().1))), input.chan_manager.allocate().0))
        },
    }
}

pub open spec fn client() -> ClientStateMachine {
    StateMachine {
        init: |s: ClientState| {
            s == ClientState {}
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
