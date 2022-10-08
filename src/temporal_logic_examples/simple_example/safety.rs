// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pred::*;
use crate::simple_example::state_machine::*;
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

spec fn happy_temp_pred() -> TempPred<SimpleState> {
    happy_state_pred().lift()
}

spec fn always_happy() -> TempPred<SimpleState> {
    implies(
        and(init_state_pred().lift(), always(next_action_pred().lift())),
        always(happy_temp_pred())
    )
}

proof fn prove_always_happy()
    ensures
        valid(always_happy())
{
    init_invariant::<SimpleState>(init_state_pred(), next_action_pred(), happy_state_pred());
}

}
