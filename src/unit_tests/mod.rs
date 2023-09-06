// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
pub mod object_meta;

use vstd::prelude::*;

verus! {

#[verifier(external)]
pub fn test() {
    println!("Running unit tests for trusted functions...");
    object_meta::test();
}

}
