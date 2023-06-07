// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::seq::*;
use vstd::seq_lib::*;

verus! {

pub proof fn seq_unequal_preserved_by_add<A>(s1: Seq<A>, s2: Seq<A>, suffix: Seq<A>)
    requires
        s1 !== s2
    ensures
        s1 + suffix !== s2 + suffix
{
    assert(!(s1 =~= s2));
    if s1.len() == s2.len() {
        let witness_idx = choose |i: int| 0 <= i < s1.len() && s1[i] !== s2[i];
        assert((s1 + suffix)[witness_idx] !== (s2 + suffix)[witness_idx]);
    } else {
        assert((s1 + suffix).len() !== (s2 + suffix).len());
    }
}

pub proof fn seq_unequal_preserved_by_add_auto<A>(suffix: Seq<A>)
    ensures
        forall |s1, s2: Seq<A>| s1 !== s2 ==> s1 + suffix !== s2 + suffix
{
    assert forall |s1, s2: Seq<A>| s1 !== s2 implies s1 + suffix !== s2 + suffix by {
        seq_unequal_preserved_by_add(s1, s2, suffix);
    };
}

}
