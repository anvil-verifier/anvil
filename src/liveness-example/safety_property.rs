// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::seq::*;
use crate::pervasive::set::*;
use crate::simple_state_machine::*;
use crate::state::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn happy(s: SimpleState) -> bool {
    s.happy
}

pub open spec fn happy_as_set() -> Set<SimpleState> {
    Set::new(|state: SimpleState| happy(state))
}


pub open spec fn always_happy() -> bool {
    valid(
        implies(
            and(
                lift_state(init_as_set()),
                always(lift_action(next_as_set()))
            ),
            always(lift_state(happy_as_set()))
        )
    )
}

proof fn prove_always_happy()
    ensures
        always_happy()
{
    init_invariant(init_as_set(), next_as_set(), happy_as_set());
}

}
