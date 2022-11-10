// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::compound_state_machine::common::*;
use crate::pervasive::set::*;
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

pub open spec fn deliver(s: NetworkState, s_prime: NetworkState, msg_ops: MessageOps) -> bool {
    &&& msg_ops.recv.is_Some() ==> s.sent_messages.contains(msg_ops.recv.get_Some_0())
    &&& s.sent_messages + msg_ops.send === s_prime.sent_messages
}

pub open spec fn next(s: NetworkState, s_prime: NetworkState, msg_ops: MessageOps) -> bool {
    deliver(s, s_prime, msg_ops)
}

}
