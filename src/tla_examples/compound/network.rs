// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::{option::*, set::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use crate::tla_examples::compound::common::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct State {
    pub sent_messages: Set<Message>,
}

pub open spec fn deliver() -> Action<State, MessageOps, ()> {
    Action {
        precondition: |msg_ops: MessageOps, s: State| {
            msg_ops.recv.is_Some() ==> s.sent_messages.contains(msg_ops.recv.get_Some_0())
        },
        transition: |msg_ops: MessageOps, s: State| {
            (State {
                sent_messages: s.sent_messages + msg_ops.send
            }, ())
        },
    }
}

pub open spec fn network() -> NetworkStateMachine<State, MessageOps> {
    NetworkStateMachine {
        init: |s: State| s.sent_messages === Set::empty(),
        deliver: deliver(),
    }
}

}
