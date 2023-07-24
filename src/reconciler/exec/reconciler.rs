// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*};
use crate::pervasive_ext::to_view::*;
use crate::reconciler::exec::{external::*, io::*};
use vstd::prelude::*;

verus! {

pub trait Reconciler<R, T, I, O, Lib>
    where I: ToView, O: ToView, Lib: ExternalLibrary<I, O>
{
    fn reconcile_init_state(&self) -> T;
    fn reconcile_core(&self, cr: &R, resp_o: Option<Response<O>>, state: T) -> (T, Option<Request<I>>);
    fn reconcile_done(&self, state: &T) -> bool;
    fn reconcile_error(&self, state: &T) -> bool;
}

}
