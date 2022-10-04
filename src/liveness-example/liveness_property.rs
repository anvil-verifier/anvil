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

spec fn a_state_pred() -> StatePred {
    StatePred::new(|state: SimpleState| state.x === ABC::A)
}

spec fn b_state_pred() -> StatePred {
    StatePred::new(|state: SimpleState| state.x === ABC::B)
}

spec fn c_state_pred() -> StatePred {
    StatePred::new(|state: SimpleState| state.x === ABC::C)
}

spec fn a_leads_to_b() -> TempPred {
    implies(
        and(always(lift_action(next_action_pred())), weak_fairness(a_b_action_pred())),
        leads_to(lift_state(a_state_pred()), lift_state(b_state_pred()))
    )
}

proof fn prove_a_leads_to_b()
    ensures
        valid(a_leads_to_b())
{
    assert forall |any_ex: Execution| implies(lift_state(a_state_pred()), enabled(a_b_action_pred())).satisfies(any_ex) by {
        if lift_state(a_state_pred()).satisfies(any_ex) {
            // We need a witness to coax Verus that there exists a a_b() action that is enabled when x_is_a()
            let witness_action = Action {
                state: any_ex[0],
                state_prime: SimpleState {
                    x: ABC::B,
                    happy: any_ex[0].happy,
                }
            };
            assert(a_b_action_pred().satisfies(witness_action) && witness_action.state === any_ex[0]);
        }
    };
    wf1(next_action_pred(), a_b_action_pred(), a_state_pred(), b_state_pred());
}

spec fn init_a() -> TempPred {
    implies(lift_state(init_state_pred()), lift_state(a_state_pred()))
}

proof fn prove_init_a()
    ensures
        valid(init_a())
{}

spec fn eventually_b() -> TempPred {
    implies(
        and(
            lift_state(init_state_pred()),
            and(always(lift_action(next_action_pred())), weak_fairness(a_b_action_pred()))
        ),
        eventually(lift_state(b_state_pred()))
    )
}

proof fn prove_eventually_b()
    ensures
        valid(eventually_b())
{
    assert forall |any_ex: Execution| eventually_b().satisfies(any_ex) by {
        if and(
            lift_state(init_state_pred()),
            and(always(lift_action(next_action_pred())), weak_fairness(a_b_action_pred()))
        ).satisfies(any_ex) {
            prove_a_leads_to_b();
            assert(implies(and(always(lift_action(next_action_pred())), weak_fairness(a_b_action_pred())), leads_to(lift_state(a_state_pred()), lift_state(b_state_pred()))).satisfies(any_ex));
            // assert(leads_to(lift_state(a_state_pred()), lift_state(b_state_pred())).satisfies(any_ex));

            prove_init_a();
            // assert(lift_state(a_state_pred()).satisfies(any_ex));

            leads_to_apply(a_state_pred(), b_state_pred());
            assert(implies(and(lift_state(a_state_pred()), leads_to(lift_state(a_state_pred()), lift_state(b_state_pred()))), eventually(lift_state(b_state_pred()))).satisfies(any_ex));
            // assert(eventually(lift_state(b_state_pred())).satisfies(any_ex));
        }
    };
}

spec fn b_leads_to_c() -> TempPred {
    implies(
        and(always(lift_action(next_action_pred())), weak_fairness(b_c_action_pred())),
        leads_to(lift_state(b_state_pred()), lift_state(c_state_pred()))
    )
}

proof fn prove_b_leads_to_c()
    ensures
        valid(b_leads_to_c())
{
    assert forall |any_ex: Execution| implies(lift_state(b_state_pred()), enabled(b_c_action_pred())).satisfies(any_ex) by {
        if lift_state(b_state_pred()).satisfies(any_ex) {
            // We need a witness to coax Verus that there exists a b_c() action that is enabled when x_is_b()
            let witness_action = Action {
                state: any_ex[0],
                state_prime: SimpleState {
                    x: ABC::C,
                    happy: any_ex[0].happy,
                }
            };
            assert(b_c_action_pred().satisfies(witness_action) && witness_action.state === any_ex[0]);
        }
    };
    wf1(next_action_pred(), b_c_action_pred(), b_state_pred(), c_state_pred());
}

spec fn a_leads_to_c() -> TempPred {
    implies(
        and(
            always(lift_action(next_action_pred())),
            and(weak_fairness(a_b_action_pred()), weak_fairness(b_c_action_pred()))
        ),
        leads_to(lift_state(a_state_pred()), lift_state(c_state_pred()))
    )
}

proof fn prove_a_leads_to_c()
    ensures
        valid(a_leads_to_c())
{
    assert forall |any_ex: Execution| a_leads_to_c().satisfies(any_ex) by {
        if and(
            and(always(lift_action(next_action_pred())), weak_fairness(a_b_action_pred())),
            weak_fairness(b_c_action_pred())
        ).satisfies(any_ex) {
            prove_a_leads_to_b();
            assert(implies(and(always(lift_action(next_action_pred())), weak_fairness(a_b_action_pred())), leads_to(lift_state(a_state_pred()), lift_state(b_state_pred()))).satisfies(any_ex));
            // assert(leads_to(lift_state(a_state_pred()), lift_state(b_state_pred())).satisfies(any_ex));

            prove_b_leads_to_c();
            assert(implies(and(always(lift_action(next_action_pred())), weak_fairness(b_c_action_pred())), leads_to(lift_state(b_state_pred()), lift_state(c_state_pred()))).satisfies(any_ex));
            // assert(leads_to(lift_state(b_state_pred()), lift_state(c_state_pred())).satisfies(any_ex));

            leads_to_trans(a_state_pred(), b_state_pred(), c_state_pred());
            assert(implies(and(leads_to(lift_state(a_state_pred()), lift_state(b_state_pred())), leads_to(lift_state(b_state_pred()), lift_state(c_state_pred()))), leads_to(lift_state(a_state_pred()), lift_state(c_state_pred()))).satisfies(any_ex));
            // assert(leads_to(lift_state(a_state_pred()), lift_state(c_state_pred())).satisfies(any_ex));
        }
    };
}

spec fn eventually_c() -> TempPred {
    implies(
        and(
            lift_state(init_state_pred()),
            and(
                always(lift_action(next_action_pred())),
                and(weak_fairness(a_b_action_pred()), weak_fairness(b_c_action_pred()))
            )
        ),
        eventually(lift_state(c_state_pred()))
    )
}

proof fn prove_eventually_c()
    ensures
        valid(eventually_c())
{
    assert forall |any_ex: Execution| eventually_c().satisfies(any_ex) by {
        if and(
            lift_state(init_state_pred()),
            and(
                always(lift_action(next_action_pred())),
                and(weak_fairness(a_b_action_pred()), weak_fairness(b_c_action_pred()))
            )
        ).satisfies(any_ex) {
            prove_a_leads_to_c();
            assert(implies(and(always(lift_action(next_action_pred())), and(weak_fairness(a_b_action_pred()), weak_fairness(b_c_action_pred()))), leads_to(lift_state(a_state_pred()), lift_state(c_state_pred()))).satisfies(any_ex));
            // assert(leads_to(lift_state(a_state_pred()), lift_state(c_state_pred())).satisfies(any_ex));

            prove_init_a();
            // assert(lift_state(a_state_pred()).satisfies(any_ex));

            leads_to_apply(a_state_pred(), c_state_pred());
            assert(implies(and(lift_state(a_state_pred()), leads_to(lift_state(a_state_pred()), lift_state(c_state_pred()))), eventually(lift_state(c_state_pred()))).satisfies(any_ex));
            // assert(eventually(lift_state(c_state_pred())).satisfies(any_ex));
        }
    };
}

}
