// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use vstd::prelude::*;

pub mod map_lib;
pub mod math;
pub mod multiset_lib;
pub mod seq_lib;
pub mod set_lib;
pub mod string_map;
pub mod string_view;
pub mod vec_lib;

verus! { spec fn trivial() ->bool {true} } // to enable --verify-module