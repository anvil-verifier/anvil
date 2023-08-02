// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_cluster::spec::message::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

// This enum is a wrapper for attaching rest id to the input and output of the external api.
// By doing this, we are able to check whether the output matches the input when conducting continue_reconcile.
#[is_variant]
pub enum ExternalComm<Input, Output> {
    Input(Input, nat),
    Output(Output, nat),
}

pub open spec fn external_output_matches_input<T: ExternalAPI>(output: ExternalComm<T::Input, T::Output>, input: ExternalComm<T::Input, T::Output>) -> bool {
    &&& output.is_Output()
    &&& input.is_Input()
    &&& output.get_Output_1() == input.get_Input_1()
}

pub struct ExternalAPIState<T: ExternalAPI> {
    pub external_api_state: T::State,
    // This field is similar to the in_flight field of the network state.
    // We use a set to accommodate the input and output of the external api which haven't been processed.
    pub in_flight: Set<ExternalComm<T::Input, T::Output>>,
}

pub open spec fn external_api_state_init<T: ExternalAPI>(s: ExternalAPIState<T>) -> bool {
    &&& s.external_api_state == T::init_state()
    &&& s.in_flight == Set::<ExternalComm<T::Input, T::Output>>::empty()
}

pub open spec fn external_api_send_output_and_receive_input<T: ExternalAPI>(
    input: Option<ExternalComm<T::Input, T::Output>>, output: Option<ExternalComm<T::Input, T::Output>>, s: ExternalAPIState<T>
) -> ExternalAPIState<T> {
    ExternalAPIState {
        in_flight: if output.is_Some() {
            if input.is_Some() {
                s.in_flight.remove(input.get_Some_0()).insert(output.get_Some_0())
            } else {
                s.in_flight.insert(output.get_Some_0())
            }
        } else {
            if input.is_Some() {
                s.in_flight.remove(input.get_Some_0())
            } else {
                s.in_flight
            }
        },
        ..s
    }
}

}
