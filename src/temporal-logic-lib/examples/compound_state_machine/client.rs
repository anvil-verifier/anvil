// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::compound_state_machine::common::*;
use crate::pervasive::{option::*, seq::*, set::*};
use crate::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct State {}

pub struct ClientInput {
    pub cr: ResourceObj,
    pub recv: Option<Message>,
}

pub enum Step {
    SendCreateCrStep(ResourceObj),
    SendDeleteCrStep(ResourceObj),
}

pub type ClientStateMachine = HostStateMachine<State, Option<Message>, ClientInput, Set<Message>, Step>;

pub type ClientAction = HostAction<State, ClientInput, Set<Message>>;

pub type ClientHostActionResult = HostActionResult<State, Set<Message>>;

pub open spec fn send_create_cr() -> ClientAction {
    HostAction {
        precondition: |i: ClientInput, s| {
            &&& i.cr.key.kind.is_CustomResourceKind()
            &&& i.recv.is_None()
        },
        transition: |i: ClientInput, s| {
            (s, set![create_req_msg(i.cr.key)])
        },
    }
}

pub open spec fn send_delete_cr() -> ClientAction {
    HostAction {
        precondition: |i: ClientInput, s| {
            &&& i.cr.key.kind.is_CustomResourceKind()
            &&& i.recv.is_None()
        },
        transition: |i: ClientInput, s| {
            (s, set![delete_req_msg(i.cr.key)])
        },
    }
}

pub open spec fn client() -> ClientStateMachine {
    HostStateMachine {
        init: |s: State| true,
        actions: set![send_create_cr(), send_delete_cr()],
        step_to_action: |step: Step| {
            match step {
                Step::SendCreateCrStep(_) => send_create_cr(),
                Step::SendDeleteCrStep(_) => send_delete_cr(),
            }
        },
        action_input: |step: Step, recv: Option<Message>| {
            match step {
                Step::SendCreateCrStep(res) => ClientInput{cr: res, recv: recv},
                Step::SendDeleteCrStep(res) => ClientInput{cr: res, recv: recv},
            }
        }
    }
}

}
