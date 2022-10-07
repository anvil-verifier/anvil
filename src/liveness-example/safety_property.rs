// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::simple_state_machine::*;
use crate::state::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

spec fn happy(s: SimpleState) -> bool {
    s.happy
}

spec fn happy_state_pred() -> StatePred<SimpleState> {
    StatePred::new(|state: SimpleState| happy(state))
}

spec fn always_happy() -> TempPred<SimpleState> {
    implies(
        and(lift_state(init_state_pred()), always(lift_action(next_action_pred()))),
        always(lift_state(happy_state_pred()))
    )
}

proof fn prove_always_happy()
    ensures
        valid(always_happy())
{
    init_invariant::<SimpleState>(init_state_pred(), next_action_pred(), happy_state_pred());
}

}
