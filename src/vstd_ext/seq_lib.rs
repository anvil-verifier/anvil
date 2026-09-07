// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;
use crate::vstd_ext::set_lib::*;

verus! {

// --- trusted --- //

// currently not provable because sort_by is closed spec
#[verifier(external_body)]
pub proof fn lemma_sort_by_does_not_add_or_delete_elements<A>(s: Seq<A>, leq: spec_fn(A, A) -> bool)
// we don't care if total_ordering(leq) holds here
    ensures s.sort_by(leq).to_set() == s.to_set(),
    decreases s.len()
{}

// --- proved ---

pub proof fn seq_unequal_preserved_by_add<A>(s1: Seq<A>, s2: Seq<A>, suffix: Seq<A>)
    requires s1 != s2
    ensures s1 + suffix != s2 + suffix
{
    assert(!(s1 =~= s2));
    if s1.len() == s2.len() {
        let witness_idx = choose |i: int| 0 <= i < s1.len() && s1[i] != s2[i];
        assert((s1 + suffix)[witness_idx] != (s2 + suffix)[witness_idx]);
    } else {
        assert((s1 + suffix).len() != (s2 + suffix).len());
    }
}

pub proof fn seq_unequal_preserved_by_add_prefix<A>(prefix: Seq<A>, s1: Seq<A>, s2: Seq<A>)
    requires s1 != s2
    ensures prefix + s1 != prefix + s2
{
    assert(!(s1 =~= s2));
    if s1.len() == s2.len() {
        let witness_idx = choose |i: int| 0 <= i < s1.len() && s1[i] != s2[i];
        let offset = prefix.len();
        assert((prefix + s1)[witness_idx + offset] != (prefix + s2)[witness_idx + offset]);
    } else {
        assert((prefix + s1).len() != (prefix + s2).len());
    }
}

pub proof fn seq_equal_preserved_by_add<A>(s1: Seq<A>, s2: Seq<A>, suffix: Seq<A>)
    ensures s1 == s2 <==> s1 + suffix == s2 + suffix
{
    assert_by(
        s1 == s2 ==> s1 + suffix == s2 + suffix,
        {
            if s1 == s2 {
                let len = s1.len();
                assert forall |i| 0<= i < (s1 + suffix).len() implies (#[trigger] (s1 + suffix)[i]) == (s2 + suffix)[i] by {
                    if i < len {
                        assert((s1 + suffix)[i] == s1[i]);
                        assert((s2 + suffix)[i] == s2[i]);
                    } else {
                        assert((s1 + suffix)[i] == suffix[i - len]);
                        assert((s2 + suffix)[i] == suffix[i - len]);
                    }
                }
            }

        }
    );
    assert_by(
        s1 + suffix == s2 + suffix ==> s1 == s2,
        {
            if s1 + suffix == s2 + suffix {
                assert((s1 + suffix).len() == (s2 + suffix).len());
                assert(s1.len() == s2.len());
                assert forall |i| 0<= i < s1.len() implies (#[trigger] s1[i]) == s2[i] by {
                    assert(s1[i] == (s1 + suffix)[i]);
                    assert(s2[i] == (s2 + suffix)[i]);
                }
                assert(s1 =~= s2);
            }
        }
    )
}

pub proof fn seq_equal_preserved_by_add_prefix<A>(prefix: Seq<A>, s1: Seq<A>, s2: Seq<A>)
    ensures s1 == s2 <==> prefix + s1 == prefix + s2
{
    assert_by(
        s1 == s2 ==> prefix + s1 == prefix + s2,
        {
            if s1 == s2 {
                let len = prefix.len();
                assert forall |i| 0<= i < (prefix + s1).len() implies (#[trigger] (prefix + s1)[i]) == (prefix + s2)[i] by {
                    if i < len {
                        assert((prefix + s1)[i] == prefix[i]);
                        assert((prefix + s2)[i] == prefix[i]);
                    } else {
                        assert((prefix + s1)[i] == s1[i - len]);
                        assert((prefix + s2)[i] == s2[i - len]);
                    }
                }
            }

        }
    );
    assert_by(
        prefix + s1 == prefix + s2 ==> s1 == s2,
        {
            if prefix + s1 == prefix + s2 {
                assert((prefix + s1).len() == (prefix + s2).len());
                assert(s1.len() == s2.len());
                let len = prefix.len();
                assert forall |i| 0<= i < s1.len() implies (#[trigger] s1[i]) == s2[i] by {
                    assert(s1[i] == (prefix + s1)[i + len]);
                    assert(s2[i] == (prefix + s2)[i + len]);
                }
                assert(s1 =~= s2);
            }
        }
    )
}

pub proof fn seq_unequal_preserved_by_add_auto<A>(suffix: Seq<A>)
    ensures forall |s1: Seq<A>, s2: Seq<A>| s1 != s2 ==> s1 + suffix != s2 + suffix
{
    assert forall |s1: Seq<A>, s2: Seq<A>| s1 != s2 implies s1 + suffix != s2 + suffix by {
        seq_unequal_preserved_by_add(s1, s2, suffix);
    };
}

pub proof fn seq_pred_false_on_all_elements_is_equivalent_to_empty_filter<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures (forall |i: int| 0 <= i < s.len() ==> !pred(#[trigger] s[i])) <==> s.filter(pred).len() == 0,
{
    if s.len() != 0 {
        if (forall |i: int| 0 <= i < s.len() ==> !pred(s[i])) {
            assert(s.all(|x: A| !pred(x)));
            s.lemma_all_neg_filter_empty(pred);
        }
        if (s.filter(pred).len() == 0) {
            empty_filter_implies_seq_pred_false_on_all_indices(s, pred);
        }
    }
}

proof fn empty_filter_implies_seq_pred_false_on_all_indices<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    requires s.filter(pred).len() == 0,
    ensures forall |i: int| 0 <= i < s.len() ==> !pred(#[trigger] s[i])
    decreases s.len()
    // If `pred` is false on every element, filter will return an empty sequence.
{
    if s.len() != 0 {
        let subseq = s.drop_last();
        assert(!pred(s.last())) by {
            // assert(s.filter(pred).len() == 0);
            reveal(Seq::filter);
            assert(s.filter(pred) == {
                if pred(s.last()) {
                    subseq.filter(pred).push(s.last())
                } else {
                    subseq.filter(pred)
                }
            })
        }
        assert(s.filter(pred) == subseq.filter(pred)) by {
            reveal(Seq::filter);
            assert(!pred(s.last()));
        }
        empty_filter_implies_seq_pred_false_on_all_indices(s.drop_last(), pred);
        assert forall |i: int| 0 <= i < s.len() implies !pred(#[trigger] s[i]) by {
            if i < subseq.len() { assert(s[i] == subseq[i]); }
        }
    }
}

pub proof fn seq_filter_preserves_no_duplicates<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    requires s.no_duplicates(),
    ensures s.filter(pred).no_duplicates()
    decreases s.len()
{
    reveal(Seq::filter);
    if s.len() != 0 {
        seq_filter_preserves_no_duplicates(s.drop_last(), pred);
        if pred(s.last()) {
            seq_filter_is_a_subset_of_original_seq(s.drop_last(), pred);
        }
    }
}

pub proof fn map_values_weakens_no_duplicates<A, B>(s: Seq<A>, map: spec_fn(A) -> B)
    requires s.map_values(map).no_duplicates()
    ensures s.no_duplicates()
{
    assert forall |i, j| 0 <= i < s.len() && 0 <= j < s.len() && i != j implies s[i] != s[j] by {
        if s[i] == s[j] {
            assert(s.map_values(map)[i] == s.map_values(map)[j]);
            assert(false);
        }
    }
}

pub proof fn seq_filter_is_a_subset_of_original_seq<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        forall |i: int| 0 <= i < s.filter(pred).len() ==> s.contains(#[trigger] s.filter(pred)[i]),
    decreases s.len()
{
    reveal(Seq::filter);
    if s.filter(pred).len() != 0 {
        let subseq = s.drop_last();
        seq_filter_is_a_subset_of_original_seq(subseq, pred);
        assert(forall |i: int| 0 <= i < subseq.filter(pred).len() ==> subseq.contains(#[trigger] subseq.filter(pred)[i]));
    }
}

pub proof fn true_pred_on_seq_implies_true_pred_on_filtered_seq<A>(s: Seq<A>, pred: spec_fn(A) -> bool, filter_pred: spec_fn(A) -> bool)
    requires forall |i: int| 0 <= i < s.len() ==> pred(#[trigger] s[i]),
    ensures forall |i: int| 0 <= i < s.filter(filter_pred).len() ==> pred(#[trigger] s.filter(filter_pred)[i]),
{
    lemma_different_filtered_elems_map_to_different_elems(s, filter_pred);
    assert forall |i: int| 0 <= i < s.filter(filter_pred).len() implies pred(#[trigger] s.filter(filter_pred)[i]) by {
        assert(s.filter(filter_pred)[i] == s[filter_idx(s, filter_pred, i)]);
    }
}

pub proof fn lemma_filter_to_set_eq_to_set_filter<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures s.filter(pred).to_set() == s.to_set().filter(pred),
    decreases s.len()
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let subseq = s.drop_last();
        lemma_filter_to_set_eq_to_set_filter(subseq, pred);
        subseq.lemma_filter_push(s.last(), pred);
        if pred(s.last()) {
            subseq.filter(pred).lemma_push_to_set_commute(s.last());
        }
    }
}

// Q: Why reveal is required as filter is open spec
pub proof fn commutativity_of_seq_map_and_filter<A, B>(s: Seq<A>, pred: spec_fn(A) -> bool, pred_on_mapped: spec_fn(B) -> bool, map: spec_fn(A) -> B)
    // ensure filter on original sequence is identical to filter on mapped sequence
    requires forall |i: int| 0 <= i < s.len() ==> #[trigger] pred(s[i]) == #[trigger] pred_on_mapped(map(s[i])),
    ensures s.map_values(map).filter(pred_on_mapped) == s.filter(pred).map_values(map),
    decreases s.len()
{
    reveal(Seq::filter);
    if s.len() != 0 {
        let subseq = s.drop_last();
        commutativity_of_seq_map_and_filter(subseq, pred, pred_on_mapped, map);
        assert(pred(s.last()) == pred_on_mapped(map(s.last())));
        assert(s.map_values(map).filter(pred_on_mapped) == s.filter(pred).map_values(map)) by {
            assert(subseq.map_values(map).filter(pred_on_mapped) == subseq.filter(pred).map_values(map));
            assert(s.map_values(map) == subseq.map_values(map).push(map(s.last())));
            assert(s.map_values(map).drop_last() == subseq.map_values(map));
            if !pred(s.last()) {
                assert(s.map_values(map).filter(pred_on_mapped) == subseq.map_values(map).filter(pred_on_mapped)) by {
                    assert(subseq.map_values(map).filter(pred_on_mapped) == subseq.map_values(map).push(map(s.last())).filter(pred_on_mapped));
                }
            } else {
                // why this line the same as postcondition is required
                assert(s.map_values(map).filter(pred_on_mapped) == s.filter(pred).map_values(map));
            }
        }
    }
}

pub proof fn commutativity_of_seq_drop_last_and_map<A, B>(s: Seq<A>, pred: spec_fn(A) -> B)
    requires s.len() > 0,
    ensures s.drop_last().map_values(pred) == s.map_values(pred).drop_last(),
    decreases s.len()
{
    broadcast use group_seq_properties;
    if s.len() > 1 {
        let subseq = s.drop_last();
        commutativity_of_seq_drop_last_and_map(subseq, pred);
        assert(s.map_values(pred).drop_last() == subseq.map_values(pred));
    } else {
        assert(s.drop_last().map_values(pred) == Seq::<B>::empty());
        assert(s.map_values(pred).drop_last() == Seq::<B>::empty());
    }
}

pub proof fn same_filter_implies_same_result<A>(s: Seq<A>, f1: spec_fn(A) -> bool, f2: spec_fn(A) -> bool)
    requires forall |i: int| 0 <= i < s.len() ==> (f1(#[trigger] s[i]) == f2(s[i])),
    ensures s.filter(f1) == s.filter(f2),
    decreases s.len()
{
    reveal(Seq::filter);
    if s.len() != 0 {
        let subseq = s.drop_last();
        assert(forall |i: int| 0 <= i < subseq.len() ==> #[trigger] subseq[i] == s[i]);
        same_filter_implies_same_result(subseq, f1, f2);
        assert(s[s.len() - 1] == s.last());
        if f1(s.last()){
            assert(f2(s.last()));
            assert(s.filter(f1) == subseq.filter(f1).push(s.last()));
            assert(s.filter(f2) == subseq.filter(f2).push(s.last()));
        } else {
            assert(!f2(s.last()));
            assert(s.filter(f1) == subseq.filter(f1));
            assert(s.filter(f2) == subseq.filter(f2));
        }
    }
}

pub proof fn lemma_homomorphism_of_map_values<A, B, C>(s: Seq<A>, f1: spec_fn(A) -> B, f2: spec_fn(B) -> C, g: spec_fn(A)->C)
    requires forall |i: int| 0 <= i < s.len() ==> f2(f1(#[trigger] s[i])) == g(s[i]),
    ensures s.map_values(g) == s.map_values(f1).map_values(f2),
    decreases s.len()
{
    if s.len() != 0 {
        let subseq = s.drop_last();
        assert(forall |i: int| 0 <= i < subseq.len() ==> #[trigger] subseq[i] == s[i]);
        lemma_homomorphism_of_map_values(subseq, f1, f2, g);
        assert(s[s.len() - 1] == s.last());
        assert(s.map_values(g) == subseq.map_values(g).push(g(s.last())));
    }
}

// Maps index i in s.filter(pred) to the corresponding index in s
pub open spec fn filter_idx<A>(s: Seq<A>, pred: spec_fn(A) -> bool, i: int) -> int
    decreases s.len()
{
    if s.len() == 0 {
        // unreachable under valid preconditions
        0
    } else if pred(s.last()) {
        if i == s.drop_last().filter(pred).len() {
            // This filtered element is the last element of s
            s.len() - 1
        } else {
            // Recurse into the prefix
            filter_idx(s.drop_last(), pred, i)
        }
    } else {
        // Last element doesn't match pred, recurse into the prefix
        filter_idx(s.drop_last(), pred, i)
    }
}

// Proves that filter_idx correctly maps filter indices to original sequence indices,
// and that the mapping is strictly monotone (preserves order).
proof fn lemma_filter_idx_properties<A>(s: Seq<A>, pred: spec_fn(A) -> bool, i: int)
    requires
        0 <= i < s.filter(pred).len(),
    ensures
        0 <= filter_idx(s, pred, i) < s.len(),
        s.filter(pred)[i] == s[filter_idx(s, pred, i)],
    decreases s.len()
{
    reveal(Seq::filter);
    if s.len() == 0 {
        // filter of empty seq is empty, so precondition is false
    } else {
        let sub = s.drop_last();
        if pred(s.last()) {
            // s.filter(pred) == sub.filter(pred).push(s.last())
            // so s.filter(pred).len() == sub.filter(pred).len() + 1
            if i == sub.filter(pred).len() {
                // This is the last element of the filtered seq, which is s.last()
                assert(s.filter(pred)[i] == s.last());
                assert(filter_idx(s, pred, i) == s.len() - 1);
            } else {
                // i < sub.filter(pred).len()
                assert(0 <= i < sub.filter(pred).len());
                lemma_filter_idx_properties(sub, pred, i);
                assert(s.filter(pred)[i] == sub.filter(pred)[i]);
            }
        } else {
            // s.filter(pred) == sub.filter(pred)
            assert(0 <= i < sub.filter(pred).len());
            lemma_filter_idx_properties(sub, pred, i);
        }
    }
}

// Proves that filter_idx is strictly monotone: i < j ==> filter_idx(s, pred, i) < filter_idx(s, pred, j)
proof fn lemma_filter_idx_strict_mono<A>(s: Seq<A>, pred: spec_fn(A) -> bool, i: int, j: int)
    requires
        0 <= i < j,
        j < s.filter(pred).len(),
    ensures
        filter_idx(s, pred, i) < filter_idx(s, pred, j),
    decreases s.len()
{
    reveal(Seq::filter);
    if s.len() == 0 {
    } else {
        let sub = s.drop_last();
        if pred(s.last()) {
            if j == sub.filter(pred).len() {
                // j maps to s.len() - 1
                // i < j = sub.filter(pred).len(), so i is in sub's filter
                lemma_filter_idx_properties(sub, pred, i);
                // filter_idx(s, pred, i) == filter_idx(sub, pred, i) < sub.len() = s.len() - 1
            } else {
                // both i and j are in sub's filter range
                assert(0 <= i < j);
                assert(j < sub.filter(pred).len());
                lemma_filter_idx_strict_mono(sub, pred, i, j);
            }
        } else {
            // s.filter(pred) == sub.filter(pred)
            lemma_filter_idx_strict_mono(sub, pred, i, j);
        }
    }
}

pub proof fn lemma_different_filtered_elems_map_to_different_elems<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
ensures
    forall |i: int| 0 <= i < s.filter(pred).len() ==>
        0 <= #[trigger] filter_idx(s, pred, i) < s.len() && s.filter(pred)[i] == s[filter_idx(s, pred, i)],
    forall |i: int, j: int| 0 <= i < s.filter(pred).len() && 0 <= j < s.filter(pred).len() && i != j ==>
        #[trigger] filter_idx(s, pred, i) != #[trigger] filter_idx(s, pred, j),
{
    assert forall |i: int| 0 <= i < s.filter(pred).len() implies
        0 <= #[trigger] filter_idx(s, pred, i) < s.len() && s.filter(pred)[i] == s[filter_idx(s, pred, i)]
    by {
        lemma_filter_idx_properties(s, pred, i);
    };
    assert forall |i: int, j: int| 0 <= i < s.filter(pred).len() && 0 <= j < s.filter(pred).len() && i != j implies
        #[trigger] filter_idx(s, pred, i) != #[trigger] filter_idx(s, pred, j)
    by {
        if i < j {
            lemma_filter_idx_strict_mono(s, pred, i, j);
        } else {
            lemma_filter_idx_strict_mono(s, pred, j, i);
        }
    };
}

}