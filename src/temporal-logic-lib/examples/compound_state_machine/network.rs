// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::compound_state_machine::common::*;
use crate::pervasive::{option::*, set::*};
use crate::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct State {
    pub sent_messages: Set<Message>,
}

pub open spec fn deliver() -> NetworkAction<State, Message> {
    NetworkAction {
        precondition: |recv: Option<Message>, s: State| {
            recv.is_Some() ==> s.sent_messages.contains(recv.get_Some_0())
        },
        transition: |recv: Option<Message>, s: State, send: Set<Message>| {
            State {
                sent_messages: s.sent_messages + send
            }
        },
    }
}

pub open spec fn network() -> NetworkStateMachine<State, Message> {
    NetworkStateMachine {
        init: |s: State| s.sent_messages === Set::empty(),
        deliver: deliver(),
    }
}

}
