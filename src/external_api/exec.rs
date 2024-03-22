// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::spec::EmptyTypeView;
use vstd::{prelude::*, view::*};

verus! {

// A trait for the external api of a reconciler, whose core is a transition method, and the developer should wrap all
// possible operations they may need in the function.
// Input is the input type of the external api and also the ? of Request<?> of the reconciler, i.e., it completes the
// request type of a reconciler.
// Similarly, Output is the output type of the external api, which composes the Response<?> type of a reconciler.
// Note that we can encapsulate all the required libraries here, so each reconciler only has one ExternalAPI type.
pub trait ExternalAPIShimLayer {
    type Input: View;
    type Output: View;
    fn call_external_api(input: Self::Input) -> Self::Output;
}

// An empty library that implements External Library.
// This can be used by those controllers that don't rely on a third-party library.
// Users can define a reconciler as Reconciler<xx, xx, EmptyType, EmptyType, EmptyAPI>.
pub struct EmptyAPIShimLayer {}

impl ExternalAPIShimLayer for EmptyAPIShimLayer {
    type Input = EmptyType;
    type Output = EmptyType;
    fn call_external_api(_input: EmptyType) -> EmptyType {
        EmptyType {}
    }
}

pub struct EmptyType {}

impl View for EmptyType {
    type V = EmptyTypeView;
    spec fn view(&self) -> EmptyTypeView;
}

}
