// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::{map_lib::*, prelude::*, seq_lib::*, set::*, set_lib::*};

verus! {

// Select all the values in m, whose keys satisfy f, into the returned seq
// TODO: implement the spec function and prove the lemma
pub closed spec fn select_map_to_seq<K, V>(m: Map<K, V>, f: FnSpec(K) -> bool) -> Seq<V>;

// #[verifier(external_body)]
// pub proof fn lemma_select_map_to_seq_membership<K, V>(m: Map<K, V>, f: FnSpec(K) -> bool)
//     ensures
//         // all the values whose keys satisfy f are in the sequence
//         forall |k: K| #[trigger] m.contains_key(k) && f(k) ==> select_map_to_seq(m, f).contains(m[k]),
//         // and the length of the filtered dom of m is the same as the length of the sequence
//         // which means the sequence does not have any other values
//         m.dom().filter(f).len() == select_map_to_seq(m, f).len(),
// {}


}
