// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use crate::tla_examples::abc::state_machine::*;
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
