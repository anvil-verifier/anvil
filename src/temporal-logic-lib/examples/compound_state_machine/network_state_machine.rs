// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::compound_state_machine::common::*;
use crate::pervasive::{option::*, set::*};
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct NetworkState {
    pub sent_messages: Set<Message>,
}

pub open spec fn init(s: NetworkState) -> bool {
    s.sent_messages === Set::empty()
}

pub open spec fn deliver() -> NetworkAction<NetworkState, Option<Message>, Set<Message>> {
    NetworkAction {
        precondition: |recv: Option<Message>, s: NetworkState| {
            recv.is_Some() ==> s.sent_messages.contains(recv.get_Some_0())
        },
        transition: |recv: Option<Message>, s: NetworkState, send: Set<Message>| {
            NetworkState {
                sent_messages: s.sent_messages + send
            }
        },
    }
}

pub open spec fn next(recv: Option<Message>, s: NetworkState, s_prime: NetworkState, send: Set<Message>) -> bool {
    deliver().satisfied_by(recv, s, s_prime, send)
}

}
