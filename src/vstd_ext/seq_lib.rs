// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;

verus! {

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

pub proof fn seq_equal_preserved_by_add<A>(s1: Seq<A>, s2: Seq<A>, suffix: Seq<A>)
    ensures s1 == s2 <==> s1 + suffix == s2 + suffix
{
    assert_by(
        s1 == s2 ==> s1 + suffix == s2 + suffix,
        {
            if s1 == s2 {
                let len = s1.len();
//                assert forall |i| 0<= i < (s1 + suffix).len() implies (#[trigger] (s1 + suffix)[i]) == (s2 + suffix)[i] by {
//                    if i < len {
////                        assert((s1 + suffix)[i] == s1[i]);
////                        assert((s2 + suffix)[i] == s2[i]);
//                    } else {
////                        assert((s1 + suffix)[i] == suffix[i - len]);
////                        assert((s2 + suffix)[i] == suffix[i - len]);
//                    }
//                }
            }

        }
    );
    assert_by(
        s1 + suffix == s2 + suffix ==> s1 == s2,
        {
            if s1 + suffix == s2 + suffix {
                assert((s1 + suffix).len() == (s2 + suffix).len());
//                assert(s1.len() == s2.len());
                assert forall |i| 0<= i < s1.len() implies (#[trigger] s1[i]) == s2[i] by {
//                    assert(s1[i] == (s1 + suffix)[i]);
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
//                assert forall |i| 0<= i < (prefix + s1).len() implies (#[trigger] (prefix + s1)[i]) == (prefix + s2)[i] by {
//                    if i < len {
////                        assert((prefix + s1)[i] == prefix[i]);
////                        assert((prefix + s2)[i] == prefix[i]);
//                    } else {
////                        assert((prefix + s1)[i] == s1[i - len]);
////                        assert((prefix + s2)[i] == s2[i - len]);
//                    }
//                }
            }

        }
    );
    assert_by(
        prefix + s1 == prefix + s2 ==> s1 == s2,
        {
            if prefix + s1 == prefix + s2 {
                assert((prefix + s1).len() == (prefix + s2).len());
//                assert(s1.len() == s2.len());
                let len = prefix.len();
                assert forall |i| 0<= i < s1.len() implies (#[trigger] s1[i]) == s2[i] by {
//                    assert(s1[i] == (prefix + s1)[i + len]);
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
    ensures (forall |e: A| #[trigger] s.contains(e) ==> !pred(e)) <==> s.filter(pred).len() == 0,
{
    if s.len() != 0 {
        assert((forall |e: A| s.contains(e) ==> !pred(e)) ==> s.filter(pred).len() == 0) by {
            // p -> q <== >!p || q
            if (forall |e: A| s.contains(e) ==> !pred(e))
            {
                seq_pred_false_on_all_elements_implies_empty_filter(s, pred);
            }
        }
        assert(s.filter(pred).len() == 0 ==> (forall |e: A| s.contains(e) ==> !pred(e))) by {
            if (s.filter(pred).len() == 0)
            {
                empty_filter_implies_seq_pred_false_on_all_elements(s, pred);
            }
        }
    }
}

proof fn seq_pred_false_on_all_elements_implies_empty_filter<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    requires forall |e: A| #![auto] s.contains(e) ==> !pred(e),
    ensures s.filter(pred).len() == 0,
    decreases s.len()
    // If `pred` is false on every element, filter will return an empty sequence.
{
    reveal(Seq::filter);
    if s.len() != 0 {
        let subseq = s.drop_last();
        // prove precondition for subseq and recursive call
        assert(forall |e: A| subseq.contains(e) ==> !pred(e)) by {
            assert(forall |i: int| 0 <= i < subseq.len() ==> s.contains(#[trigger] s[i]) ==> !pred(subseq[i]));
        }
        seq_pred_false_on_all_elements_implies_empty_filter(subseq, pred);
        assert(subseq.filter(pred) == s.filter(pred)) by {
            assert(!pred(s.last())) by {
                assert(s.contains(s.last()) ==> !pred(s.last()));
            };
        } // s.filter(pred) == subseq.filter(pred) == ... == Seq::empty()
    }
}

proof fn empty_filter_implies_seq_pred_false_on_all_elements<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    requires s.filter(pred).len() == 0,
    ensures forall |e: A| #![auto] s.contains(e) ==> !pred(e)
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
//            assert(!pred(s.last()));
        }
        empty_filter_implies_seq_pred_false_on_all_elements(s.drop_last(), pred);
        assert forall |e: A| #![auto] s.contains(e) ==> !pred(e) by {
            assert(forall |i: int| 0 <= i < subseq.len() ==> (subseq.contains(#[trigger] subseq[i]) ==> !pred(subseq[i])));
            assert(forall |i: int| 0 <= i < subseq.len() ==> s[i] == subseq[i]);
            // assert(!pred(s.last()) && s.contains(s.last()));
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

pub proof fn seq_filter_contains_implies_seq_contains<A>(s: Seq<A>, pred: spec_fn(A) -> bool, elt: A)
    requires s.filter(pred).contains(elt),
    ensures s.contains(elt)
{
    seq_filter_is_a_subset_of_original_seq(s, pred);
}

// useful theorem to prove the 2 above
pub proof fn seq_filter_is_a_subset_of_original_seq<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        forall |e: A| s.filter(pred).contains(e) ==> #[trigger] s.contains(e),
        forall |i: int| 0 <= i < s.filter(pred).len() ==> s.contains(#[trigger] s.filter(pred)[i]), // 2nd form
    decreases s.len()
{
    reveal(Seq::filter);
    if s.filter(pred).len() != 0 {
        let subseq = s.drop_last();
        seq_filter_is_a_subset_of_original_seq(subseq, pred);
        assert(forall |i: int| 0 <= i < subseq.filter(pred).len() ==> subseq.contains(#[trigger] subseq.filter(pred)[i]));
        // assert(forall |i: int| 0 <= i < s.filter(pred).len() ==> s.contains(#[trigger] s.filter(pred)[i]));
        // assert(forall |e: A| s.filter(pred).contains(e) ==> #[trigger] s.contains(e));
    }
}

// TODO: remove this lemma
pub proof fn seq_map_value_lemma<A, B>(s: Seq<A>, f: spec_fn(A) -> B)
    ensures 
        s.len() == s.map_values(f).len(),
        (forall |i: int| 0 <= i < s.len() ==> #[trigger] s.map_values(f)[i] == f(s[i]))
{}
}
