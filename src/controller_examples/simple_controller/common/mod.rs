// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus! {

#[is_variant]
pub enum SimpleReconcileStep {
    Init,
    AfterCreateConfigMap,
    Done,
    Error,
}

}
