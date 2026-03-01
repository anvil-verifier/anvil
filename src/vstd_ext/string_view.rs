// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

use vstd::prelude::*;
use crate::vstd_ext::seq_lib::*;

verus! {

pub type StringView = Seq<char>;

// helper function to circumvent the lack of support for String in spec
#[verifier(external_body)]
pub fn string_equal(s1: &String, s2: &str) -> (res: bool)
    ensures
        s1@ == s2@ <==> res,
{
    s1 == s2
}

#[verifier(external_body)]
pub fn i32_to_string(i: i32) -> (s: String)
    ensures s@ == int_to_string_view(i as int),
{
    i.to_string()
}

#[verifier(external_body)]
pub fn usize_to_string(i: usize) -> (s: String) 
    ensures s@ == int_to_string_view(i as int)
{
    i.to_string()
}

pub uninterp spec fn int_to_string_view(i: int) -> StringView;

#[verifier(external_body)]
pub proof fn int_to_string_view_injectivity()
    ensures forall |i: int, j: int| int_to_string_view(i) == int_to_string_view(j) ==> i == j,
{}

#[verifier(external_body)]
pub proof fn int_to_string_view_dash_free()
    ensures forall |i: int| dash_free(#[trigger] int_to_string_view(i)),
{}

#[verifier(external_body)]
pub fn bool_to_string(b: bool) -> (s: String)
    ensures s@ == bool_to_string_view(b),
{
    b.to_string()
}

pub uninterp spec fn bool_to_string_view(b: bool) -> StringView;

#[verifier(external_body)]
pub proof fn bool_to_string_view_injectivity()
    ensures forall |i: bool, j: bool| bool_to_string_view(i) == bool_to_string_view(j) ==> i == j,
{}

pub open spec fn opt_string_to_view(s: &Option<String>) -> Option<StringView> {
    match s {
        Some(s1) => Some(s1@),
        None => None,
    }
}

pub open spec fn dash_free(s: Seq<char>) -> bool {
    forall |i: int| 0 <= i < s.len() ==> s[i] != '-'@
}

#[verifier(external_body)]
pub fn dash_free_exec(s: &String) -> (res: bool)
    ensures res == dash_free(s@)
{
    !s.as_str().contains("-")
}

// helper function to circumvent the lack of support for String in spec
#[verifier(external_body)]
pub proof fn dash_char_view_eq_str_view() 
    ensures "-"@ == seq!['-'@],
{}

pub proof fn lemma_dash_free_prefix_preserves_suffix_inequality(
    a1: Seq<char>, a2: Seq<char>, b1: Seq<char>, b2: Seq<char>,
)
requires
    dash_free(a1),
    dash_free(a2),
    b1 != b2,
ensures
    a1 + "-"@ + b1 != a2 + "-"@ + b2
{
    let lhs = a1 + "-"@ + b1;
    let rhs = a2 + "-"@ + b2;
    dash_char_view_eq_str_view();
    if a1 != a2 {
        if a1.len() == a2.len() {
            if forall |i: int| 0 <= i < a1.len() ==> a1[i] == a2[i] {
                assert(a1 == a2);
                assert(false);
            }
            let witness_idx = choose |i: int| 0 <= i < a1.len() && a1[i] != a2[i];
            assert(lhs[witness_idx] != rhs[witness_idx]);
        } else if a1.len() < a2.len() {
            let witness_idx = a1.len() as int;
            assert(lhs[witness_idx] == '-'@);
            assert(rhs[witness_idx] != '-'@);
        } else {
            let witness_idx = a2.len() as int;
            assert(lhs[witness_idx] != '-'@);
            assert(rhs[witness_idx] == '-'@);
        }
    } else {
        seq_equal_preserved_by_add(a1, a2, "-"@);
        seq_unequal_preserved_by_add_prefix(a1 + "-"@, b1, b2);
    }
}

pub proof fn lemma_dash_free_suffix_preserves_prefix_inequality(
    a1: Seq<char>, a2: Seq<char>, b1: Seq<char>, b2: Seq<char>,
)
requires
    dash_free(b1),
    dash_free(b2),
    a1 != a2,
ensures
    a1 + "-"@ + b1 != a2 + "-"@ + b2
{
    let lhs = a1 + "-"@ + b1;
    let rhs = a2 + "-"@ + b2;
    dash_char_view_eq_str_view();
    if lhs == rhs {
        assert(lhs.len() == rhs.len());
        assert(a1.len() + b1.len() + 1 == a2.len() + b2.len() + 1);
        if a1.len() == a2.len() {
            if forall |i: int| 0 <= i < a1.len() ==> a1[i] == a2[i] {
                assert(a1 == a2);
                assert(false);
            }
            let witness_idx = choose |i: int| 0 <= i < a1.len() && a1[i] != a2[i];
            assert(lhs[witness_idx] != rhs[witness_idx]);
        } else if a1.len() < a2.len() {
            let witness_idx = a2.len() as int;
            assert(rhs[witness_idx] == '-'@);
            assert(lhs[witness_idx] == b1[witness_idx - a1.len() - 1]);
            assert(lhs[witness_idx] != '-'@);
        } else {
            let witness_idx = a1.len() as int;
            assert(lhs[witness_idx] == '-'@);
            assert(rhs[witness_idx] == b2[witness_idx - a2.len() - 1]);
            assert(rhs[witness_idx] != '-'@);
        }
    }
}

}