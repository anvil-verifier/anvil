// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::compound_state_machine::common::*;
use crate::pervasive::{option::*, seq::*, set::*};
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct ClientState {}

pub open spec fn init(s: ClientState) -> bool {
    true
}

pub struct ClientInput {
    pub cr: ResourceObj,
    pub recv: Option<Message>,
}

pub open spec fn send_create_cr() -> HostAction<ClientState, ClientInput, Set<Message>> {
    HostAction {
        precondition: |i: ClientInput, s| {
            &&& i.cr.key.kind.is_CustomResourceKind()
            &&& i.recv.is_None()
        },
        transition: |i: ClientInput, s| {
            s
        },
        output: |i: ClientInput, s| {
            set![create_req_msg(i.cr.key)]
        }
    }
}

pub open spec fn send_delete_cr() -> HostAction<ClientState, ClientInput, Set<Message>> {
    HostAction {
        precondition: |i: ClientInput, s| {
            &&& i.cr.key.kind.is_CustomResourceKind()
            &&& i.recv.is_None()
        },
        transition: |i: ClientInput, s| {
            s
        },
        output: |i: ClientInput, s| {
            set![delete_req_msg(i.cr.key)]
        }
    }
}

pub enum ClientStep {
    SendCreateCrStep(ResourceObj),
    SendDeleteCrStep(ResourceObj),
}

pub open spec fn next_step(recv: Option<Message>, s: ClientState, s_prime: ClientState, send: Set<Message>, step: ClientStep) -> bool {
    match step {
        ClientStep::SendCreateCrStep(res) => send_create_cr().satisfied_by(ClientInput{cr: res, recv: recv}, s, s_prime, send),
        ClientStep::SendDeleteCrStep(res) => send_delete_cr().satisfied_by(ClientInput{cr: res, recv: recv}, s, s_prime, send),
    }
}

pub open spec fn next(recv: Option<Message>, s: ClientState, s_prime: ClientState, send: Set<Message>) -> bool {
    exists |step| next_step(recv, s, s_prime, send, step)
}

}
