// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::{map_lib::*, prelude::*, seq_lib::*, set::*, set_lib::*};

verus! {

// Select all the values in m, whose keys satisfy f, into the returned seq
// TODO: implement the spec function and prove the lemma
pub closed spec fn select_map_to_seq<K, V>(m: Map<K, V>, f: FnSpec(K) -> bool) -> Seq<V>;

#[verifier(external_body)]
pub proof fn lemma_select_map_to_seq_membership<K, V>(m: Map<K, V>, f: FnSpec(K) -> bool)
    ensures
        // all the values whose keys satisfy f are in the sequence
        forall |k: K| #[trigger] m.contains_key(k) && f(k) ==> select_map_to_seq(m, f).contains(m[k]),
        // and the length of the filtered dom of m is the same as the length of the sequence
        // which means the sequence does not have any other values
        m.dom().filter(f).len() == select_map_to_seq(m, f).len(),
{}

pub proof fn union_prefer_right_self_changes_nothing<K, V>()
    ensures
        forall |map: Map<K, V>|
            map.union_prefer_right(map) =~= map,
{}

// // TODO: We will use the Verus native lemma_values_finite once we update to the most recent Verus.
// pub proof fn lemma_values_finite<K, V>(m: Map<K, V>)
//     requires m.dom().finite(),
//     ensures m.values().finite(),
//     decreases m.len(),
// {
//     if m.len() > 0 {
//         let k = m.dom().choose();
//         let v = m[k];
//         let m1 = m.remove(k);
//         assert(m.contains_key(k));
//         assert(m.contains_value(v));
//         assert_sets_equal!(m.values() == m1.values().insert(v), v0 => {
//             if m.values().contains(v0) {
//                 assert(m1.values().insert(v).contains(v0));
//             }
//             if m1.values().insert(v).contains(v0) {
//                 if v0 == v {
//                     assert(m.contains_value(v));
//                     assert(m.values().contains(v0));
//                 } else {
//                     assert(m.values().contains(v0));
//                 }
//             }
//         });
//         assert(m1.len() < m.len());
//         lemma_values_finite(m1);
//         axiom_set_insert_finite(m1.values(), v);
//     } else {
//         assert(m.values() =~= Set::<V>::empty());
//     }
// }

}
