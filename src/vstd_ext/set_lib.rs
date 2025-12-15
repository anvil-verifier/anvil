// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::set::*;
use vstd::set_lib::*;
use crate::vstd_ext::map_lib::*;

verus! {

pub proof fn lemma_filter_set<A>(s: Set<A>, f: spec_fn(A) -> bool)
ensures
    forall |a: A| #[trigger] s.filter(f).contains(a) ==> {
        &&& f(a)
        &&& s.contains(a)
    }
{}

pub proof fn finite_set_to_finite_filtered_set<A>(s: Set<A>, f: spec_fn(A) -> bool)
    requires s.finite(),
    ensures s.filter(f).finite(),
    decreases s.len()
{
    if s.len() != 0 {
        let x = s.choose();
        finite_set_to_finite_filtered_set(s.remove(x), f);
    }
}

pub proof fn finite_set_to_seq_contains_all_set_elements<A>(s: Set<A>)
    requires s.finite(),
    ensures forall |e: A| #[trigger] s.contains(e) <==> #[trigger] s.to_seq().contains(e)
{
    if s.len() != 0 {
        assert forall |e: A| #[trigger] s.contains(e) implies s.to_seq().contains(e) by {
            element_in_finite_set_exists_in_set_to_seq(s, e);
        }
        assert forall |e: A| #[trigger] s.to_seq().contains(e) implies s.contains(e) by {
            element_in_seq_exists_in_original_finite_set(s, e);
        }
    }
}

pub proof fn finite_set_to_seq_has_no_duplicates<A>(s: Set<A>)
    requires s.finite(),
    ensures s.to_seq().no_duplicates(),
    decreases s.len()
{
    reveal(Set::to_seq);
    if s.len() != 0 {
        let x = s.choose();
        finite_set_to_seq_has_no_duplicates(s.remove(x));
        finite_set_to_seq_contains_all_set_elements(s.remove(x));
        assert(!s.remove(x).to_seq().contains(x));
    }
}

pub proof fn element_in_finite_set_exists_in_set_to_seq<A>(s: Set<A>, e: A)
    requires s.finite(), s.contains(e),
    ensures s.to_seq().contains(e),
    decreases s.len()
{
    if s.len() != 0 {
        // need choose() to be not-random
        let x = s.choose();
        if x == e {
            assert(s.to_seq() == Seq::empty().push(e) + s.remove(e).to_seq());
            assert(s.to_seq()[0] == e);
        } else {
            element_in_finite_set_exists_in_set_to_seq(s.remove(x), e);
            assert(s.to_seq().subrange(1, s.to_seq().len() as int) == s.remove(x).to_seq());
        }
    }
}

pub proof fn element_in_seq_exists_in_original_finite_set<A>(s: Set<A>, e: A)
    requires s.finite(), s.to_seq().contains(e),
    ensures s.contains(e),
    decreases s.len()
{
    if s.len() != 0 {
        // need choose() to be not-random
        let x = s.choose();
        if x != e {
            element_in_seq_exists_in_original_finite_set(s.remove(x), e);
        }
    }
}

pub proof fn lemma_mk_map_insert_k<A, B>(m: Set<A>, k: A, map: spec_fn(A) -> B)
    ensures m.insert(k).mk_map(map) == m.mk_map(map).insert(k, map(k)),
{
    assert(m.insert(k).mk_map(map).contains_pair(k, map(k)));
    assert(m.insert(k).mk_map(map) =~= m.mk_map(map).insert(k, map(k))) by {
        assert forall |key: A| #[trigger] m.insert(k).mk_map(map).contains_key(key) implies m.mk_map(map).insert(k, map(k)).contains_key(key) by {
            if key == k {
                assert(m.mk_map(map).insert(k, map(k)).contains_key(k));
            } else {
                assert(m.mk_map(map).contains_key(key));
            }
        }
        assert forall |key: A| #[trigger] m.mk_map(map).insert(k, map(k)).contains_key(key) implies m.insert(k).mk_map(map).contains_key(key) by {
            if key == k {
                assert(m.insert(k).mk_map(map).contains_key(k));
            } else {
                assert(m.mk_map(map).contains_key(key));
            }
        }
    }
}

pub proof fn lemma_to_seq_to_set_equal<A>(s: Set<A>)
    requires s.finite(),
    ensures s.to_seq().to_set() == s,
{
    finite_set_to_seq_contains_all_set_elements(s);
}
}