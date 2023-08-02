// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::spec::message::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub trait ExternalAPI {

    type Input;
    type Output;
    type State;

    open spec fn transition(input: Self::Input, state: Self::State) -> (Option<Self::Output>, Self::State);

    open spec fn init_state() -> Self::State;
}

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
    pub in_flight: Set<ExternalComm<T::Input, T::Output>>,
}

pub open spec fn external_api_state_init<T: ExternalAPI>(s: ExternalAPIState<T>) -> bool {
    &&& s.external_api_state == T::init_state()
    &&& s.in_flight == Set::<ExternalComm<T::Input, T::Output>>::empty()
}

pub struct EmptyType {}

pub struct EmptyAPI {}

impl ExternalAPI for EmptyAPI {

    type Input = EmptyType;
    type Output = EmptyType;
    type State = EmptyType;

    open spec fn transition(input: EmptyType, state: EmptyType) -> (Option<EmptyType>, EmptyType) {
        (Option::None, EmptyType{})
    }

    open spec fn init_state() -> EmptyType {
        EmptyType {}
    }
}

}
