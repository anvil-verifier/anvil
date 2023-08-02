// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::pervasive_ext::to_view::*;
use vstd::prelude::*;

verus! {

pub trait ExternalAPI {

    type Input;
    type Output;
    type State;

    open spec fn transition(input: Self::Input, state: Self::State) -> (Option<Self::Output>, Self::State);

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
