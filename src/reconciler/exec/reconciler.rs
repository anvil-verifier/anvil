// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*};
use crate::reconciler::exec::io::*;
use vstd::{prelude::*, view::*};

verus! {

pub trait Reconciler<R, T, ReceiverType: View, ResponseType: View> {
    fn reconcile_init_state(&self) -> T;
    fn reconcile_core(&self, cr: &R, resp_o: Option<Response<ResponseType>>, state: T) -> (T, Option<Receiver<ReceiverType>>);
    fn reconcile_done(&self, state: &T) -> bool;
    fn reconcile_error(&self, state: &T) -> bool;
    fn helper_functions(&self, receiver: ReceiverType) -> Option<ResponseType>;
}

}
