// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::spec::EmptyTypeView;
use crate::pervasive_ext::to_view::*;
use vstd::{prelude::*, view::*};

verus! {

// A trait for the external library of a reconciler.
// Its core is a process method, and the developer should wrap all possible operations they may need in the function.
// Input is the ? of Request<?> of the reconciler, i.e., it completes the request type of a reconciler.
// Similarly, Output composes the Response<?> type of a reconciler.
// Note that we can encapsulate all the required libraries here, so each reconciler only has one ExternalAPI type.
pub trait ExternalAPI<Input: ToView, Output: ToView> {
    fn transition(input: Input) -> Option<Output>;
}

// An empty library that implements External Library.
// This can be used by those controllers that don't rely on a third-party library.
// Users can define a reconciler as Reconciler<xx, xx, EmptyType, EmptyType, EmptyAPI>.
pub struct EmptyAPI {}

impl ExternalAPI<EmptyType, EmptyType> for EmptyAPI {
    fn transition(input: EmptyType) -> Option<EmptyType> {
        Option::None
    }
}

pub struct EmptyType {}

impl ToView for EmptyType {
    type V = EmptyTypeView;
    spec fn to_view(&self) -> EmptyTypeView;
}

}
