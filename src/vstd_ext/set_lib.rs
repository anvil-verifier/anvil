// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::set::*;
use vstd::set_lib::*;

verus! {

#[verifier(external_body)]
pub proof fn finite_set_to_seq_contains_all_set_elements<A>(s: Set<A>)
    requires s.finite(),
    ensures forall |e: A| #![auto] s.contains(e) <==> s.to_seq().contains(e);
//
// TODO: Prove this -- Trivial.
// 
// Anything in a finite set will be in a sequence composed of its elements; likewise
// anything in that constructed sequence will be part of the original set.
//

#[verifier(external_body)]
pub proof fn finite_set_to_seq_has_no_duplicates<A>(s: Set<A>)
    requires s.finite(),
    ensures s.to_seq().no_duplicates();
//
// TODO: Prove this -- Trivial.
// 
// The `to_seq()` construction applied to a set will not introduce duplicates.
//

}
