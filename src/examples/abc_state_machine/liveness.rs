// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::abc_state_machine::state_machine::*;
use crate::temporal_logic::*;
use crate::temporal_logic_rules::*;
use builtin::*;
use builtin_macros::*;

verus! {

proof fn eventually_c()
    ensures
        sm_spec().entails(
            eventually(lift_state(c()))
        ),
{
    // a_b_enabled() gives a witness to convince Verus that x === A enables a_b()
    a_b_enabled();
    // wf1 gives us a leads_to
    wf1::<SimpleState>(sm_spec(), next(), a_b(), a(), b());

    // a_b_enabled() gives a witness to convince Verus that x === B enables b_c()
    b_c_enabled();
    // wf1 gives us another leads_to
    wf1::<SimpleState>(sm_spec(), next(), b_c(), b(), c());

    // leads_to_trans connects the two leads_to together
    leads_to_trans::<SimpleState>(sm_spec(), a(), b(), c());

    // leads_to_apply gives us eventually from leads_to
    leads_to_apply::<SimpleState>(sm_spec(), a(), c());
}

}
