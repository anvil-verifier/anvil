// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::api_method::*;
use crate::reconciler::exec::io::*;
use crate::reconciler::spec::io::*;
use vstd::prelude::*;

verus! {

pub trait Reconciler{
    type R;
    type T;
    type ExternalAPIType: ExternalAPIShimLayer;
    spec fn well_formed(cr: &Self::R) -> bool;
    fn reconcile_init_state() -> Self::T;
    fn reconcile_core(cr: &Self::R, resp_o: Option<Response<<Self::ExternalAPIType as ExternalAPIShimLayer>::Output>>, state: Self::T) -> (Self::T, Option<Request<<Self::ExternalAPIType as ExternalAPIShimLayer>::Input>>)
        requires Self::well_formed(cr);
    fn reconcile_done(state: &Self::T) -> bool;
    fn reconcile_error(state: &Self::T) -> bool;
}

}
