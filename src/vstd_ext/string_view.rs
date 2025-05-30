// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

use vstd::prelude::*;

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

pub uninterp spec fn int_to_string_view(i: int) -> StringView;

#[verifier(external_body)]
pub proof fn int_to_string_view_injectivity()
    ensures forall |i: int, j: int| int_to_string_view(i) == int_to_string_view(j) ==> i == j,
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

}
