use crate::kubernetes_cluster::spec::message::*;
use crate::kubernetes_cluster::spec::network::types::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub open spec fn deliver() -> Action<NetworkState, MessageOps, ()> {
    Action {
        precondition: |msg_ops: MessageOps, s: NetworkState| {
            msg_ops.recv is Some ==> s.in_flight.contains(msg_ops.recv->0)
        },
        transition: |msg_ops: MessageOps, s: NetworkState| {
            if msg_ops.recv is Some {
                let s_prime = NetworkState {
                    in_flight: s.in_flight.remove(msg_ops.recv->0).add(msg_ops.send)
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
        init: |s: NetworkState| s.in_flight == Multiset::<Message>::empty(),
        deliver: deliver(),
    }
}

}
