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

pub proof fn map_values_to_set_eq_to_set_mk_map_values<A, B>(s: Seq<A>, map: spec_fn(A) -> B)
    ensures s.map_values(map).to_set() == s.to_set().mk_map(map).values(),
    decreases s.len()
{
    if s.len() != 0 {
        let subseq = s.drop_last();
        map_values_to_set_eq_to_set_mk_map_values(subseq, map);
        assert(s.map_values(map).to_set() == subseq.map_values(map).to_set().insert(map(s.last()))) by {
            push_to_set_eq_to_set_insert(subseq.map_values(map), map(s.last()));
            assert(s.map_values(map) == subseq.map_values(map).push(map(s.last())));
        }
        let submap = subseq.to_set().mk_map(map);
        assert(s.map_values(map).to_set() == submap.values().insert(map(s.last())));
        assert(s.to_set().mk_map(map).values() == submap.values().insert(map(s.last()))) by {
            push_to_set_eq_to_set_insert(subseq, s.last());
            assert(s == subseq.push(s.last()));
            assert(s.to_set() == subseq.to_set().insert(s.last()));
            lemma_mk_map_insert_k(subseq.to_set(), s.last(), map);
            assert(subseq.to_set().insert(s.last()).mk_map(map) == submap.insert(s.last(), map(s.last())));
            assert(s.to_set().mk_map(map) == submap.insert(s.last(), map(s.last())));
            if subseq.to_set().contains(s.last()) {
                assert(submap.contains_pair(s.last(), map(s.last())));
                assert(submap.values().contains(map(s.last())));
                assert(submap.values().insert(map(s.last())) == submap.values());
                assert(s.to_set() == subseq.to_set());
                assert(s.to_set().mk_map(map).values() == submap.values());
            } else {
                assert(submap.values().insert(map(s.last())) =~= submap.insert(s.last(), map(s.last())).values()) by {
                    assert forall |v: B| #[trigger] submap.values().insert(map(s.last())).contains(v)
                           implies submap.insert(s.last(), map(s.last())).contains_value(v) by {
                        if v != map(s.last()) {
                            assert(submap.contains_value(v));
                            assert(exists |k: A| #[trigger] submap.contains_key(k) && #[trigger] submap[k] == v);
                            let k = choose |k: A| #[trigger] submap.contains_key(k) && #[trigger] submap[k] == v;
                            assert(k != s.last()) by {
                                assert(!subseq.to_set().contains(s.last()));
                                assert(!submap.contains_key(s.last()));
                                assert(submap.contains_key(k));
                            }
                            assert(submap.insert(s.last(), map(s.last())).contains_pair(k, v));
                            assert(submap.insert(s.last(), map(s.last())).contains_value(v));
                        } else {
                            assert(submap.insert(s.last(), map(s.last())).contains_pair(s.last(), map(s.last())));
                        }
                    }
                    assert(submap.insert(s.last(), map(s.last())).contains_pair(s.last(), map(s.last())));
                    assert(submap.insert(s.last(), map(s.last())).values().contains(map(s.last())));
                    assert forall |v: B| #[trigger] submap.insert(s.last(), map(s.last())).values().contains(v)
                           implies submap.values().insert(map(s.last())).contains(v) by {
                        if v != map(s.last()) {
                            assert(submap.contains_value(v));
                        }
                    } 
                }
            }
        }
    }
    assert(s.map_values(map).to_set() == s.to_set().mk_map(map).values()); // why it's required
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

}