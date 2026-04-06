// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use vstd::prelude::*;

pub mod exec;
pub mod model;
pub mod proof;
pub mod trusted;

verus! { spec fn trivial() ->bool {true} } // makes verus recognize this as a mod