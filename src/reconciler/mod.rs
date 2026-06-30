// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use vstd::prelude::*;

pub mod exec;
pub mod spec;

verus! { spec fn trivial() ->bool {true} } // to enable --verify-module