// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use vstd::{prelude::*, view::*};

verus! {

pub trait ExternalLibrary<InputType: View, OutputType: View> {
    fn process(input: InputType) -> Option<OutputType>;
}

pub struct EmptyLib {}

impl ExternalLibrary<EmptyMsg, EmptyMsg> for EmptyLib {
    fn process(input: EmptyMsg) -> Option<EmptyMsg> {
        Option::None
    }
}

pub struct EmptyMsg {}

type EmptyMsgView = ();

impl View for EmptyMsg {
    type V = EmptyMsgView;
    spec fn view(&self) -> EmptyMsgView;
}

}
