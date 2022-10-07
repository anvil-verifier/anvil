// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::simple_state_machine::*;
use crate::state::*;
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
    implies(sm_spec(), eventually(lift_state(c_state_pred())))
}

proof fn prove_eventually_c()
    ensures
        valid(eventually_c())
{
    // apply_implies_auto is used to automatically apply the following rule:
    // valid(implies(p, q)) && p.satisfied_by(ex) ==> q.satisfied_by(ex)
    // without requiring the developer to write `assert forall |ex| ... implies ... by {...}` in the proof
    apply_implies_auto::<SimpleState>();

    // a_b_enabled() gives a witness to convince Verus that x === a enables a_b()
    a_b_enabled();
    // wf1 gives us a leads_to
    wf1::<SimpleState>(next_action_pred(), a_b_action_pred(), a_state_pred(), b_state_pred());
    // Now we have:
    // assert(valid(implies(sm_spec(), leads_to(lift_state(a_state_pred()), lift_state(b_state_pred())))));

    // a_b_enabled() gives a witness to convince Verus that x === b enables b_c()
    b_c_enabled();
    // wf1 gives us another leads_to
    wf1::<SimpleState>(next_action_pred(), b_c_action_pred(), b_state_pred(), c_state_pred());
    // Now we have:
    // assert(valid(implies(sm_spec(), leads_to(lift_state(b_state_pred()), lift_state(c_state_pred())))));

    // leads_to_trans connects the two leads_to together
    leads_to_trans::<SimpleState>(a_state_pred(), b_state_pred(), c_state_pred());
    // Now we have:
    // assert(valid(implies(sm_spec(), leads_to(lift_state(a_state_pred()), lift_state(c_state_pred())))));

    leads_to_apply::<SimpleState>(a_state_pred(), c_state_pred());
    // Now we have:
    // assert(valid(implies(sm_spec(), eventually(lift_state(c_state_pred())))));
}

}
