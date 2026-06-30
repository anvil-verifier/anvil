// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use vstd::prelude::*;

pub mod state_machine;
pub mod action;

verus! { spec fn trivial() ->bool {true} } // to enable --verify-module