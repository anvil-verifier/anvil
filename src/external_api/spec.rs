// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::{common::*, dynamic::*};
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
    spec fn transition(input: Self::Input, resources: StoredState, state: Self::State) -> (Self::State, Self::Output);

    // init_state gives the initial state of the external api.
    spec fn init_state() -> Self::State;
}

pub struct EmptyTypeView {}

pub struct EmptyAPI {}

impl ExternalAPI for EmptyAPI {

    type Input = EmptyTypeView;
    type Output = EmptyTypeView;
    type State = EmptyTypeView;

    open spec fn transition(input: EmptyTypeView, resources: StoredState, state: EmptyTypeView) -> (EmptyTypeView, EmptyTypeView) {
        (EmptyTypeView {}, EmptyTypeView {})
    }

    open spec fn init_state() -> EmptyTypeView {
        EmptyTypeView {}
    }
}

}
