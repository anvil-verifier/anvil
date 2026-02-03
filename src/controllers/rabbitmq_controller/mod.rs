// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use vstd::prelude::*;

pub mod exec;
pub mod model;
pub mod proof;
pub mod trusted;

verus! { #[verifier(external_body)] proof fn trivial() {} } // makes verus recognize this as a mod