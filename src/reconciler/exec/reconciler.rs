// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*};
use crate::reconciler::exec::{external::*, io::*};
use vstd::{prelude::*, view::*};

verus! {

pub trait Reconciler<R, T, LibInputType, LibOutputType, Lib>
    where LibInputType: View, LibOutputType: View, Lib: ExternalLibrary<LibInputType, LibOutputType>
{
    fn reconcile_init_state(&self) -> T;
    fn reconcile_core(&self, cr: &R, resp_o: Option<Response<LibOutputType>>, state: T) -> (T, Option<Receiver<LibInputType>>);
    fn reconcile_done(&self, state: &T) -> bool;
    fn reconcile_error(&self, state: &T) -> bool;
}

}
