// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use vstd::{prelude::*, view::*};

verus! {

// A trait for the external library of a reconciler.
// Its core is a process method, and the developer should wrap all possible operations they may need in the function.
// The InputType is the ? of Request<?> of the reconciler, i.e., it completes the request type of a reconciler.
// Similarly, the OutputType composes the Response<?> type of a reconciler.
// Note that we can encapsulate all the required libraries here, so each reconciler only has one ExternalLibrary type.
pub trait ExternalLibrary<InputType: View, OutputType: View> {
    fn process(input: InputType) -> Option<OutputType>;
}

// An empty library that implements External Library.
// This can be used by those controllers that don't rely on a third-party library.
// Users can define a reconciler as Reconciler<xx, xx, EmptyMsg, EmptyMsg, EmptyLib>.
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
