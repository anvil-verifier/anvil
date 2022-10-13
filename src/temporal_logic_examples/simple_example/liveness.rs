// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::simple_example::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

spec fn a_state_pred() -> StatePred<SimpleState> {
    StatePred::new(|state: SimpleState| state.x === ABC::A)
}

spec fn b_state_pred() -> StatePred<SimpleState> {
    StatePred::new(|state: SimpleState| state.x === ABC::B)
}

spec fn c_state_pred() -> StatePred<SimpleState> {
    StatePred::new(|state: SimpleState| state.x === ABC::C)
}

spec fn a_temp_pred() -> TempPred<SimpleState> {
    a_state_pred().lift()
}

spec fn b_temp_pred() -> TempPred<SimpleState> {
    b_state_pred().lift()
}

spec fn c_temp_pred() -> TempPred<SimpleState> {
    c_state_pred().lift()
}

proof fn a_b_enabled()
    ensures forall |s: SimpleState| #[trigger] a_state_pred().satisfied_by(s) <==> enabled(a_b_action_pred()).satisfied_by(s)
{
    assert forall |s: SimpleState| #[trigger] a_state_pred().satisfied_by(s) implies enabled(a_b_action_pred()).satisfied_by(s) by {
        let witness_action = Action {
            state: s,
            state_prime: SimpleState {
                x: ABC::B,
                happy: s.happy,
            }
        };
        assert(a_b_action_pred().satisfied_by(witness_action));
    };
}

proof fn b_c_enabled()
    ensures forall |s: SimpleState| #[trigger] b_state_pred().satisfied_by(s) <==> enabled(b_c_action_pred()).satisfied_by(s)
{
    assert forall |s: SimpleState| #[trigger] b_state_pred().satisfied_by(s) implies enabled(b_c_action_pred()).satisfied_by(s) by {
        let witness_action = Action {
            state: s,
            state_prime: SimpleState {
                x: ABC::C,
                happy: s.happy,
            }
        };
        assert(b_c_action_pred().satisfied_by(witness_action));
    }
}

spec fn eventually_c() -> TempPred<SimpleState> {
    sm_spec().implies(eventually(c_temp_pred()))
}

proof fn prove_eventually_c()
    ensures
        valid(eventually_c())
{
    // implies_apply_auto is used to automatically apply the following rule:
    // valid(implies(p, q)) && p.satisfied_by(ex) ==> q.satisfied_by(ex)
    // without requiring the developer to write `assert forall |ex| ... implies ... by {...}` in the proof
    implies_apply_auto::<SimpleState>();

    // a_b_enabled() gives a witness to convince Verus that x === a enables a_b()
    a_b_enabled();
    // wf1 gives us a leads_to
    wf1::<SimpleState>(next_action_pred(), a_b_action_pred(), a_state_pred(), b_state_pred());
    // Now we have:
    // assert(valid(implies(sm_spec(), leads_to(a_temp_pred(), b_temp_pred()))));

    // a_b_enabled() gives a witness to convince Verus that x === b enables b_c()
    b_c_enabled();
    // wf1 gives us another leads_to
    wf1::<SimpleState>(next_action_pred(), b_c_action_pred(), b_state_pred(), c_state_pred());
    // Now we have:
    // assert(valid(implies(sm_spec(), leads_to(b_temp_pred(), c_temp_pred()))));

    // leads_to_trans connects the two leads_to together
    leads_to_trans::<SimpleState>(sm_spec(), a_state_pred().lift(), b_state_pred().lift(), c_state_pred().lift());
    // Now we have:
    // assert(valid(implies(sm_spec(), leads_to(a_temp_pred(), c_temp_pred()))));

    // leads_to_apply gives us eventually from leads_to
    // Note that init_state_pred(), as part of sm_spec(), implies a_temp_pred()
    leads_to_apply::<SimpleState>(sm_spec(), a_state_pred().lift(), c_state_pred().lift());
    // Now we have:
    // assert(valid(implies(sm_spec(), eventually(c_temp_pred()))));
}

}
