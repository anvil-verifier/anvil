// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::spec::common::*;
use crate::pervasive::{multiset::*, option::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct NetworkState {
    pub in_flight: Multiset<Message>,
}

pub open spec fn deliver() -> Action<NetworkState, MessageOps<Message>, ()> {
    Action {
        precondition: |msg_ops: MessageOps<Message>, s: NetworkState| {
            msg_ops.recv.is_Some() ==> multiset_contains_msg(s.in_flight, msg_ops.recv.get_Some_0())
        },
        transition: |msg_ops: MessageOps<Message>, s: NetworkState| {
            if msg_ops.recv.is_Some() {
                let s_prime = NetworkState {
                    in_flight: s.in_flight.remove(msg_ops.recv.get_Some_0()).add(msg_ops.send)
                };
                (s_prime, ())
            } else {
                let s_prime = NetworkState {
                    in_flight: s.in_flight.add(msg_ops.send)
                };
                (s_prime, ())
            }
        },
    }
}

pub open spec fn network() -> NetworkStateMachine<NetworkState, Message> {
    NetworkStateMachine {
        init: |s: NetworkState| s.in_flight === Multiset::empty(),
        deliver: deliver(),
    }
}

}
