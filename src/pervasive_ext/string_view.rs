// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

use vstd::prelude::*;
use vstd::string::*;

verus! {

pub type StringView = Seq<char>;

#[verifier(external_body)]
pub fn u32_to_string(u: u32) -> (s: String)
    ensures
        s@ == nat_to_string_view(u as nat),
{
    String::from_rust_string(u.to_string())
}

pub closed spec fn nat_to_string_view(n: nat) -> StringView;

#[verifier(external_body)]
pub proof fn nat_to_string_view_injectivity()
    ensures
        forall |i: nat, j: nat| nat_to_string_view(i) == nat_to_string_view(j) ==> i == j,
{}

pub closed spec fn int_to_string_view(i: int) -> StringView;

#[verifier(external_body)]
pub proof fn int_to_string_view_injectivity()
    ensures
        forall |i: int, j: int| int_to_string_view(i) == int_to_string_view(j) ==> i == j,
{}

}
