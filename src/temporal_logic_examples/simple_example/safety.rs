// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
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

proof fn prove_always_happy()
    ensures
        valid(sm_spec().implies(always(happy_temp_pred())))
{
    init_invariant::<SimpleState>(sm_spec(), init_state_pred(), next_action_pred(), happy_state_pred());
}

}
