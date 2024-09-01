// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::types::*;
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::resource::*;
use crate::kubernetes_cluster::spec::{cluster::Cluster, message::*};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

impl <K: CustomResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn deliver() -> Action<NetworkState<E::Input, E::Output>, MessageOps<E::Input, E::Output>, ()> {
    Action {
        precondition: |msg_ops: MessageOps<E::Input, E::Output>, s: NetworkState<E::Input, E::Output>| {
            msg_ops.recv.is_Some() ==> s.in_flight.contains(msg_ops.recv.get_Some_0())
        },
        transition: |msg_ops: MessageOps<E::Input, E::Output>, s: NetworkState<E::Input, E::Output>| {
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

pub open spec fn network() -> NetworkStateMachine<NetworkState<E::Input, E::Output>, MessageOps<E::Input, E::Output>> {
    NetworkStateMachine {
        init: |s: NetworkState<E::Input, E::Output>| s.in_flight == Multiset::<MsgType<E>>::empty(),
        deliver: Self::deliver(),
    }
}

}

}
