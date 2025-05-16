// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub open spec fn option_vec_view<T: View>(o: Option<Vec<T>>) -> Option<Seq<T::V>> {
    match o {
        Some(vec) => Some(vec@.map_values(|t: T| t@)),
        None => None,
    }
}

}
