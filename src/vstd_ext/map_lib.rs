// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::{map_lib::*, prelude::*, seq_lib::*, set::*, set_lib::*};

verus! {

pub proof fn lemma_equiv_filters_on_keys_and_values_implies_equiv_results<K, V>(m: Map<K, V>, f: spec_fn(K) -> bool, g: spec_fn(V) -> bool, v_k_map: spec_fn(V) -> K)
requires
    m.is_injective(),
    forall |k: K| #[trigger] m.contains_key(k) ==> f(k) == g(m[k]),
    forall |v: V| #[trigger] m.values().contains(v) ==> #[trigger] m.contains_key(v_k_map(v)) && m[v_k_map(v)] == v,
ensures
    m.dom().filter(f) == m.values().filter(g).map(v_k_map),
{   
    assert forall |elem: K| #[trigger] m.dom().filter(f).contains(elem) <==> m.values().filter(g).map(v_k_map).contains(elem) by {
        if (m.dom().filter(f).contains(elem)) {            
            assert(m.contains_key(elem));
            let v = m[elem];
            assert(m.values().filter(g).contains(v));            
            let elem_prime = v_k_map(v);
            assert(m.contains_key(elem_prime));
            assert(m[elem_prime] == m[elem]);
            assert(elem_prime == elem);
            assert(m.values().filter(g).map(v_k_map).contains(elem));
        }
        if (m.values().filter(g).map(v_k_map).contains(elem)) {
            // Verus can handle this case without any hints it seems
        }
    }
}
}
