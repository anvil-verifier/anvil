// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

use vstd::prelude::*;
use vstd::string::*;

verus! {

pub type StringView = Seq<char>;

#[verifier(external_body)]
pub fn i32_to_string(i: i32) -> (s: String)
    ensures
        s@ == int_to_string_view(i as int),
{
    String::from_rust_string(i.to_string())
}

pub closed spec fn int_to_string_view(i: int) -> StringView;

#[verifier(external_body)]
pub proof fn int_to_string_view_injectivity()
    ensures
        forall |i: int, j: int| int_to_string_view(i) == int_to_string_view(j) ==> i == j,
{}

#[verifier(external_body)]
pub proof fn int_to_string_view_ensures()
    ensures
        forall |n: int| {
            forall |i| 
                0 <= i < int_to_string_view(n).len() ==> {
                    &&& int_to_string_view(n)[i] == '0'
                    &&& int_to_string_view(n)[i] == '1'
                    &&& int_to_string_view(n)[i] == '2'
                    &&& int_to_string_view(n)[i] == '3'
                    &&& int_to_string_view(n)[i] == '4'
                    &&& int_to_string_view(n)[i] == '5'
                    &&& int_to_string_view(n)[i] == '6'
                    &&& int_to_string_view(n)[i] == '7'
                    &&& int_to_string_view(n)[i] == '8'
                    &&& int_to_string_view(n)[i] == '9'
                }
        },
{}

#[verifier(external_body)]
pub fn bool_to_string(b: bool) -> (s: String)
    ensures
        s@ == bool_to_string_view(b),
{
    String::from_rust_string(b.to_string())
}

pub closed spec fn bool_to_string_view(b: bool) -> StringView;

#[verifier(external_body)]
pub proof fn bool_to_string_view_injectivity()
    ensures
        forall |i: bool, j: bool| bool_to_string_view(i) == bool_to_string_view(j) ==> i == j,
{}

#[verifier(external_body)]
pub proof fn bool_to_string_view_ensures()
    ensures
        forall |i: bool| bool_to_string_view(i) == new_strlit("true")@ || bool_to_string_view(i) == new_strlit("false")@,
{}

pub open spec fn opt_string_to_view(s: &Option<String>) -> Option<StringView> {
    match s {
        Some(s1) => Some(s1@),
        None => None,
    }
}

}
