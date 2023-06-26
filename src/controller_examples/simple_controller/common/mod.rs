// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

#[is_variant]
pub enum SimpleReconcileStep {
    Init,
    AfterCreateConfigMap,
    Error,
}

}
