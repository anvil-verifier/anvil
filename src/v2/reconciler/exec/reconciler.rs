// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::exec::api_method::*;
use crate::reconciler::exec::io::*;
use crate::reconciler::spec::io::*;
use vstd::prelude::*;

verus! {

pub trait Reconciler {
    type S;
    type K;
    type EReq: View;
    type EResp: View;
    spec fn well_formed(cr: &Self::K) -> bool;
    fn reconcile_init_state() -> Self::S;
    fn reconcile_core(cr: &Self::K, resp_o: Option<Response<Self::EResp>>, state: Self::S) -> (Self::S, Option<Request<Self::EReq>>)
        requires Self::well_formed(cr);
    fn reconcile_done(state: &Self::S) -> bool;
    fn reconcile_error(state: &Self::S) -> bool;
}

}
