// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::{map_lib::*, prelude::*, seq_lib::*, set::*, set_lib::*};

verus! {

// Return all the values in m, which satisfy f, as a seq
pub open spec fn map_to_seq<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool) -> Seq<V> {
    m.values().filter(f).to_seq()
}

}
