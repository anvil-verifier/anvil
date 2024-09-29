// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub open spec fn option_view<T: View>(t: Option<T>) -> Option<T::V> {
    match t {
        Some(v) => Some(v@),
        None => None,
    }
}

}
