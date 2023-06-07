// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::multiset::*;

verus! {

pub proof fn len_is_zero_if_count_for_each_value_is_zero<V>(m: Multiset<V>)
    requires
        forall |v| m.count(v) == 0,
    ensures
        m.len() == 0,
{
    if m.len() != 0 {
        assert(m.count(m.choose()) > 0);
    }
}

}
