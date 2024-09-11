// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::{map_lib::*, prelude::*, seq_lib::*, set::*, set_lib::*};

verus! {

// Return all the values in m, which satisfy f, as a seq
pub open spec fn map_to_seq<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool) -> Seq<V> {
    m.values().filter(f).to_seq()
}

#[verifier(external_body)]
pub proof fn a_submap_of_a_finite_map_is_finite<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires 
        m1.submap_of(m2),
        m2.dom().finite(),
    ensures m1.dom().finite();
//
// TODO: Prove this -- Trivial.
//
// A submap of a finite map is in turn finite.
//


}
