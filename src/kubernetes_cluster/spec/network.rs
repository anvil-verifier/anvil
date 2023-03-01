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

// TODO: this can be better replaced by a Multiset::contains() method with some axioms
pub open spec fn multiset_contains_msg(mset: Multiset<Message>, m: Message) -> bool {
    mset.count(m) > 0
}

pub struct NetworkState {
    pub in_flight: Multiset<Message>,
}

pub open spec fn deliver() -> Action<NetworkState, MessageOps, ()> {
    Action {
        precondition: |msg_ops: MessageOps, s: NetworkState| {
            msg_ops.recv.is_Some() ==> multiset_contains_msg(s.in_flight, msg_ops.recv.get_Some_0())
        },
        transition: |msg_ops: MessageOps, s: NetworkState| {
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

pub open spec fn network() -> NetworkStateMachine<NetworkState, MessageOps> {
    NetworkStateMachine {
        init: |s: NetworkState| s.in_flight === Multiset::empty(),
        deliver: deliver(),
    }
}

}
