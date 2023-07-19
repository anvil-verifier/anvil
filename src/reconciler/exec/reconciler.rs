// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*};
use crate::pervasive_ext::to_view::*;
use crate::reconciler::exec::{external::*, io::*};
use vstd::{prelude::*, view::*};

verus! {

pub trait Reconciler<R, T, LibInputType, LibOutputType, Lib>
    where LibInputType: ToView, LibOutputType: ToView, Lib: ExternalLibrary<LibInputType, LibOutputType>
{
    fn reconcile_init_state(&self) -> T;
    fn reconcile_core<'a, 'b>(&'a self, cr: &'b R, resp_o: Option<Response<LibOutputType>>, state: T) -> (T, Option<Request<LibInputType>>);
    fn reconcile_done(&self, state: &T) -> bool;
    fn reconcile_error(&self, state: &T) -> bool;
}

}
