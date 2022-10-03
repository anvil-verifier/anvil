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

pub open spec fn happy_state_pred() -> StatePred {
    Set::new(|state: SimpleState| happy(state))
}

pub open spec fn always_happy() -> TempPred {
    implies(and(lift_state(init_state_pred()), always(lift_action(next_action_pred()))), always(lift_state(happy_state_pred())))
}

proof fn prove_always_happy()
    ensures
        valid(always_happy())
{
    init_invariant(init_state_pred(), next_action_pred(), happy_state_pred());
}

}
