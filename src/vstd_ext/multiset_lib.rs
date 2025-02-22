// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::{multiset::*, prelude::*};

verus! {

pub proof fn len_is_zero_means_count_for_each_value_is_zero<V>(m: Multiset<V>)
    ensures (forall |v| m.count(v) == 0) == (m.len() == 0),
{
    if m.len() != 0 {
        assert(m.count(m.choose()) > 0);
    }
}

pub proof fn filtered_size_is_zero_means_no_such_value<V>(m: Multiset<V>, f: spec_fn(V) -> bool)
    ensures (m.filter(f).len() == 0) == (forall |v: V| !(#[trigger] m.contains(v) && f(v)))
{
    if forall |v: V| !(#[trigger] m.contains(v) && f(v)) {
        assert forall |v| m.filter(f).count(v) == 0 by {
            if m.contains(v) {
//                assert(!f(v));
            }
        }
        len_is_zero_means_count_for_each_value_is_zero(m.filter(f));
    }

    if !forall |v: V| !(#[trigger] m.contains(v) && f(v)) {
        let v = choose |v| m.contains(v) && f(v);
        assert(m.filter(f).contains(v));
    }
}

pub proof fn filtered_size_is_one_means_only_one_such_value<V>(m: Multiset<V>, f: spec_fn(V) -> bool)
    ensures
        (m.filter(f).len() == 1) == {
            &&& exists |v| #[trigger] m.contains(v) && f(v)
            &&& forall |v| #[trigger] m.contains(v) && f(v) ==> {
                &&& m.count(v) == 1
                &&& forall |u: V| #[trigger] m.contains(u) && f(u) ==> u == v
            }
        }
{
    if m.filter(f).len() == 1 {
        len_is_zero_means_count_for_each_value_is_zero(m.filter(f));
        let v = m.filter(f).choose();
        assert(m.contains(v) && f(v));

//        assert forall |v| #[trigger] m.contains(v) && f(v) implies m.count(v) == 1 by {
//            if m.count(v) == 0 {
////                assert(!m.contains(v))
//            }
//            if m.count(v) > 1 {
//                assert(m.filter(f).count(v) > 1);
////                assert(m.filter(f).len() > 1);
//            }
//        }
        assert forall |v| #[trigger] m.contains(v) && f(v)
        implies (forall |u| #[trigger] m.contains(u) && f(u) ==> v == u) by {
            assert forall |u| #[trigger] m.contains(u) && f(u) implies v == u by {
                if v != u {
                    assert(m.filter(f).remove(v).len() == 0);
                    assert(!m.filter(f).remove(v).contains(u));
//                    assert(!m.filter(f).contains(u));
                }
            }
        }
    }

    if m.filter(f).len() != 1 {
        if m.filter(f).len() == 0 {
            filtered_size_is_zero_means_no_such_value(m, f);
        }
        if m.filter(f).len() > 1 {
            assert forall |v| #[trigger] m.contains(v) && f(v) && m.count(v) == 1
            implies !(forall |u: V| #[trigger] m.contains(u) && f(u) ==> u == v) by {
                assert(m.filter(f).remove(v).len() > 0);
                let u = m.filter(f).remove(v).choose();
                assert(m.filter(f).remove(v).contains(u) && m.contains(u) && f(u));
//                assert(u != v);
            }
        }
    }
}

}
