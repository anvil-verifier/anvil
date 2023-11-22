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

}
