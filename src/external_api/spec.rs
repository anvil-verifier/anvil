// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::pervasive_ext::to_view::*;
use vstd::prelude::*;

verus! {

pub trait ExternalAPI {

    // Input: type of the request (input) to the external api
    // Output: type of the response (output) from the external api
    // State: type of the state of the external api
    type Input;
    type Output;
    type State;

    // transition describes the complete logic of external apis, which is a spec counterpart of ExternalAPI::process.
    // This method consumes the input (which should be computed by reconcile_core) and the current state of the external
    // api and produces the response and the next state of the api.
    open spec fn transition(input: Self::Input, state: Self::State) -> (Option<Self::Output>, Self::State);

    // init_state gives the initial state of the external api.
    open spec fn init_state() -> Self::State;
}

pub struct EmptyTypeView {}

pub struct EmptyAPI {}

impl ExternalAPI for EmptyAPI {

    type Input = EmptyTypeView;
    type Output = EmptyTypeView;
    type State = EmptyTypeView;

    open spec fn transition(input: EmptyTypeView, state: EmptyTypeView) -> (Option<EmptyTypeView>, EmptyTypeView) {
        (Option::None, EmptyTypeView{})
    }

    open spec fn init_state() -> EmptyTypeView {
        EmptyTypeView {}
    }
}

}
