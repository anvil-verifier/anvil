// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use vstd::prelude::*;

pub mod defs;
pub mod rules;

verus! { spec fn trivial() ->bool {true} } // to enable --verify-module