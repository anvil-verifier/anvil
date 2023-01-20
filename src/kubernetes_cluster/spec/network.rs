// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::state_machine::action::*;
use crate::kubernetes_cluster::spec::common::*;
use crate::pervasive::{option::*, set::*};
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct NetworkState {
    pub sent_messages: Set<Message>,
}

pub open spec fn deliver() -> Action<NetworkState, MessageOps<Message>, ()> {
    Action {
        precondition: |msg_ops: MessageOps<Message>, s: NetworkState| {
            msg_ops.recv.is_Some() ==> s.sent_messages.contains(msg_ops.recv.get_Some_0())
        },
        transition: |msg_ops: MessageOps<Message>, s: NetworkState| {
            (NetworkState {
                sent_messages: s.sent_messages + msg_ops.send
            }, ())
        },
    }
}

pub open spec fn network() -> NetworkStateMachine<NetworkState, Message> {
    NetworkStateMachine {
        init: |s: NetworkState| s.sent_messages === Set::empty(),
        deliver: deliver(),
    }
}

}
