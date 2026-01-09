// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;
use crate::vstd_ext::set_lib::*;

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
            assert(!pred(s.last()));
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

// opposite direction of lemma_no_dup_set_cardinality
pub proof fn no_dup_seq_to_set_cardinality<A>(s: Seq<A>)
    requires s.no_duplicates(),
    ensures s.len() == s.to_set().len(),
    decreases s.len(),
{
    if s.len() != 0 {
        let subseq = s.drop_last();
        no_dup_seq_to_set_cardinality(subseq);
        push_to_set_eq_to_set_insert(subseq, s.last());
        assert(s == subseq.push(s.last()));
        if s.to_set().len() == subseq.to_set().len() {
            if !subseq.to_set().contains(s.last()) {
                assert(!subseq.contains(s.last()));
                assert(false);
            } else {
                assert(subseq.contains(s.last()));
                assert(false);
            }
        }
    } else {
        assert(s.len() == 0);
        s.lemma_cardinality_of_empty_set_is_0();
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

pub proof fn true_pred_on_seq_implies_true_pred_on_filtered_seq<A>(s: Seq<A>, pred: spec_fn(A) -> bool, filter_pred: spec_fn(A) -> bool)
    requires forall |e: A| s.contains(e) ==> pred(e),
    ensures forall |e: A| s.filter(filter_pred).contains(e) ==> pred(e)
{
    assert(forall |e: A| s.filter(filter_pred).contains(e) ==> pred(e)) by {
        assert(forall |e: A| s.filter(filter_pred).contains(e) ==> #[trigger] s.contains(e)) by {
            seq_filter_is_a_subset_of_original_seq(s, filter_pred);
        }
        assert(forall |e: A| s.contains(e) ==> pred(e));
    }
}

pub proof fn true_pred_on_all_element_equal_to_pred_on_all_index<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        (forall |obj: A| #[trigger] s.contains(obj) ==> pred(obj)) <==> (forall |i: int| 0 <= i < s.len() ==> pred(s[i]))
{
    if s.len() != 0 {
        assert((forall |i: int| 0 <= i < s.len() ==> pred(s[i])) ==> (forall |obj: A| s.contains(obj) ==> pred(obj)));
        assert((forall |obj: A| s.contains(obj) ==> pred(obj)) ==> (forall |i: int| 0 <= i < s.len() ==> pred(s[i]))) by {
            if (forall |obj: A| s.contains(obj) ==> pred(obj)) {
                assert(forall |i: int| 0 <= i < s.len() ==> pred(s[i])) by {
                    assert(forall |i: int| 0 <= i < s.len() ==> s.contains(#[trigger] s[i]) ==> pred(s[i]));
                }
            }
        }
    }
}

pub proof fn push_to_set_eq_to_set_insert<A>(s: Seq<A>, e: A)
    ensures s.push(e).to_set() == s.to_set().insert(e)
{
    assert(s.push(e).to_set() =~= s.to_set().insert(e)) by {
        assert forall |obj: A| s.push(e).to_set().contains(obj) implies #[trigger] s.to_set().insert(e).contains(obj) by {
            assert(s.push(e).contains(obj));
            if obj == e {
                assert(s.to_set().insert(e).contains(e));
            } else {
                assert(s.contains(obj));
                assert(s.to_set().contains(obj));
                assert(s.to_set().insert(e).contains(obj));
            }
        }
        assert forall |obj: A| s.to_set().insert(e).contains(obj) implies #[trigger] s.push(e).to_set().contains(obj) by {
            if obj == e {
                assert(s.push(e).last() == e); // why this trivial line is required
                assert(s.push(e).contains(e));
            } else {
                assert(s.to_set().contains(obj));
                assert(s.contains(obj));
                assert(s == s.push(e).drop_last());
            }
        }
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
        lemma_filter_push(subseq, pred, s.last());
        if pred(s.last()) {
            push_to_set_eq_to_set_insert(subseq.filter(pred), s.last());
        }
    }
}

pub proof fn lemma_filter_push<A>(s: Seq<A>, pred: spec_fn(A) -> bool, e: A)
    ensures
        pred(e) ==> s.push(e).filter(pred) == s.filter(pred).push(e),
        !pred(e) ==> s.push(e).filter(pred) == s.filter(pred),
{
    reveal(Seq::filter);
    assert(s.push(e).drop_last() == s);
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
    requires forall |e: A| #[trigger] s.contains(e) ==> (f1(e) == f2(e)),
    ensures s.filter(f1) == s.filter(f2),
    decreases s.len()
{
    reveal(Seq::filter);
    if s.len() != 0 {
        let subseq = s.drop_last();
        assert(forall |e: A| #[trigger] subseq.contains(e) ==> s.contains(e));
        same_filter_implies_same_result(subseq, f1, f2);
        assert(s.contains(s.last()));
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
    requires forall |e: A| #[trigger] s.contains(e) ==> f2(f1(e)) == g(e),
    ensures s.map_values(g) == s.map_values(f1).map_values(f2),
    decreases s.len()
{
    if s.len() != 0 {
        let subseq = s.drop_last();
        assert(forall |e: A| #[trigger] subseq.contains(e) ==> s.contains(e));
        lemma_homomorphism_of_map_values(subseq, f1, f2, g);    
        assert(s.contains(s.last()));
        assert(s.map_values(g) == subseq.map_values(g).push(g(s.last())));
    }
}

// currently not provable because sort_by is closed spec
#[verifier(external_body)]
pub proof fn lemma_sort_by_does_not_add_or_delete_elements<A>(s: Seq<A>, leq: spec_fn(A, A) -> bool)
// we don't care if total_ordering(leq) holds here
    ensures s.sort_by(leq).to_set() == s.to_set(),
    decreases s.len()
{}
}