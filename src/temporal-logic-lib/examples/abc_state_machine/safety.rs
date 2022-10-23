// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::abc_state_machine::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

proof fn always_happy()
    ensures
        sm_spec().entails(
            always(lift_state(|s: SimpleState| s.happy))
        ),
{
    init_invariant::<SimpleState>(sm_spec(),
        init(),
        next(),
        |s: SimpleState| s.happy
    );
}

}
