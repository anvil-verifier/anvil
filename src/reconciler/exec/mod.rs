// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*};
use builtin::*;
use builtin_macros::*;
use vstd::option::*;

verus! {

pub trait Reconciler<R, T> {
    fn reconcile_init_state(&self) -> T;
    fn reconcile_core(&self, cr: &R, resp_o: Option<KubeAPIResponse>, state: T) -> (T, Option<KubeAPIRequest>);
    fn reconcile_done(&self, state: &T) -> bool;
    fn reconcile_error(&self, state: &T) -> bool;
}

}
