// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::{api_method::*, common::*};
use crate::reconciler::exec::io::*;
use crate::vstd_ext::to_view::*;
use vstd::prelude::*;

verus! {

pub trait Reconciler<R, T, ExternalAPIInput, ExternalAPIOutput, ExternalAPIType>
    where ExternalAPIInput: ToView, ExternalAPIOutput: ToView, ExternalAPIType: ExternalAPIShimLayer<ExternalAPIInput, ExternalAPIOutput>
{
    fn reconcile_init_state(&self) -> T;
    fn reconcile_core(&self, cr: &R, resp_o: Option<Response<ExternalAPIOutput>>, state: T) -> (T, Option<Request<ExternalAPIInput>>);
    fn reconcile_done(&self, state: &T) -> bool;
    fn reconcile_error(&self, state: &T) -> bool;
}

}
