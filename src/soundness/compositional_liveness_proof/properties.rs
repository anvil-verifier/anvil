// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub closed spec fn a_property<S>() -> TempPred<S>;

pub closed spec fn b_property<S>() -> TempPred<S>;

}
