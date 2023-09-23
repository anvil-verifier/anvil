// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use vstd::prelude::*;

verus! {

pub trait ToView {
    type V;
    spec fn to_view(&self) -> Self::V;
}

}
