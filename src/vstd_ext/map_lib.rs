// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::{map_lib::*, prelude::*, seq_lib::*, set::*, set_lib::*};

verus! {

pub proof fn a_submap_of_a_finite_map_is_finite<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        m1.submap_of(m2),
        m2.dom().finite(),
    ensures
        m1.dom().finite(),
{
    assert(m1.dom() === m2.dom().intersect(m1.dom()));
}

pub proof fn injective_finite_map_implies_dom_len_is_equal_to_values_len<K, V>(m: Map<K, V>)
    requires
        m.dom().finite(),
        m.is_injective(),
    ensures
        m.values().finite(),
        m.dom().len() == m.values().len(),
    decreases
        m.dom().len(),
{
    if m.dom().len() == 0 {
        assert(forall |k: K| !m.dom().contains(k));
        assert(forall |v: V| !m.values().contains(v));
        assert(m.values() =~= Set::empty());
    } else {
        let key = m.dom().choose();
        let value = m[key];
        let singleton_value = Set::empty().insert(value);
        let submap = m.remove(key);

        injective_finite_map_implies_dom_len_is_equal_to_values_len(submap);
        assert forall |v: V| #[trigger] submap.contains_value(v) && m.is_injective() implies v != value by {
            let k = choose |i: K| #[trigger] submap.dom().contains(i) && submap[i] == v;
            assert(k != key);
        }

        lemma_values_finite(submap);
        assert(m.values() =~= submap.values().union(singleton_value));
        lemma_set_disjoint_lens(submap.values(), singleton_value);
        assert(m.values().len() == submap.values().len() + 1);
    }
}

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
