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

spec fn a_state_pred() -> StatePred<SimpleState> {
    StatePred::new(|state: SimpleState| state.x === ABC::A)
}

spec fn b_state_pred() -> StatePred<SimpleState> {
    StatePred::new(|state: SimpleState| state.x === ABC::B)
}

spec fn c_state_pred() -> StatePred<SimpleState> {
    StatePred::new(|state: SimpleState| state.x === ABC::C)
}

spec fn a_leads_to_b() -> TempPred<SimpleState> {
    implies(
        and(always(lift_action(next_action_pred())), weak_fairness(a_b_action_pred())),
        leads_to(lift_state(a_state_pred()), lift_state(b_state_pred()))
    )
}

/// Proves `|= []next /\ WF(a_b) => (a ~> b)`

proof fn prove_a_leads_to_b()
    ensures
        valid(a_leads_to_b())
{
    assert forall |any_ex: Execution<SimpleState>| implies(lift_state(a_state_pred()), tla_enabled(a_b_action_pred())).satisfied_by(any_ex) by {
        if lift_state(a_state_pred()).satisfied_by(any_ex) {
            // We need a witness to coax Verus that there exists a a_b() action that is enabled when x_is_a()
            let witness_action = Action {
                state: any_ex(0),
                state_prime: SimpleState {
                    x: ABC::B,
                    happy: any_ex(0).happy,
                }
            };
            assert(a_b_action_pred().satisfied_by(witness_action) && witness_action.state === any_ex(0));
        }
    };
    wf1::<SimpleState>(next_action_pred(), a_b_action_pred(), a_state_pred(), b_state_pred());
}

spec fn init_a() -> TempPred<SimpleState> {
    implies(lift_state(init_state_pred()), lift_state(a_state_pred()))
}

/// Proves `|= init => a`

proof fn prove_init_a()
    ensures
        valid(init_a())
{}

spec fn eventually_b() -> TempPred<SimpleState> {
    implies(
        and(
            lift_state(init_state_pred()),
            and(always(lift_action(next_action_pred())), weak_fairness(a_b_action_pred()))
        ),
        eventually(lift_state(b_state_pred()))
    )
}

/// Proves `|= init /\ []next /\ WF(a_b) => <> b`

proof fn prove_eventually_b()
    ensures
        valid(eventually_b())
{
    assert forall |any_ex: Execution<SimpleState>| eventually_b().satisfied_by(any_ex) by {
        if and(
            lift_state(init_state_pred()),
            and(always(lift_action(next_action_pred())), weak_fairness(a_b_action_pred()))
        ).satisfied_by(any_ex) {
            prove_a_leads_to_b();
            assert(implies(
                and(always(lift_action(next_action_pred())), weak_fairness(a_b_action_pred())),
                leads_to(lift_state(a_state_pred()), lift_state(b_state_pred()))
            ).satisfied_by(any_ex));
            // assert(leads_to(lift_state(a_state_pred()), lift_state(b_state_pred())).satisfied_by(any_ex));

            prove_init_a();
            // assert(lift_state(a_state_pred()).satisfied_by(any_ex));

            leads_to_apply(a_state_pred(), b_state_pred());
            assert(implies(
                and(
                    lift_state(a_state_pred()),
                    leads_to(lift_state(a_state_pred()), lift_state(b_state_pred()))
                ),
                eventually(lift_state(b_state_pred()))
            ).satisfied_by(any_ex));
            // assert(eventually(lift_state(b_state_pred())).satisfied_by(any_ex));
        }
    };
}

spec fn b_leads_to_c() -> TempPred<SimpleState> {
    implies(
        and(always(lift_action(next_action_pred())), weak_fairness(b_c_action_pred())),
        leads_to(lift_state(b_state_pred()), lift_state(c_state_pred()))
    )
}

/// Proves `|= []next /\ WF(b_c) => (b ~> c)`

proof fn prove_b_leads_to_c()
    ensures
        valid(b_leads_to_c())
{
    assert forall |any_ex: Execution<SimpleState>| implies(lift_state(b_state_pred()), tla_enabled(b_c_action_pred())).satisfied_by(any_ex) by {
        if lift_state(b_state_pred()).satisfied_by(any_ex) {
            // We need a witness to coax Verus that there exists a b_c() action that is enabled when x_is_b()
            let witness_action = Action {
                state: any_ex(0),
                state_prime: SimpleState {
                    x: ABC::C,
                    happy: any_ex(0).happy,
                }
            };
            assert(b_c_action_pred().satisfied_by(witness_action) && witness_action.state === any_ex(0));
        }
    };
    wf1::<SimpleState>(next_action_pred(), b_c_action_pred(), b_state_pred(), c_state_pred());
}

spec fn weak_fairness_assumption() -> TempPred<SimpleState> {
    and(weak_fairness(a_b_action_pred()), weak_fairness(b_c_action_pred()))
}

spec fn a_leads_to_c() -> TempPred<SimpleState> {
    implies(
        and(always(lift_action(next_action_pred())), weak_fairness_assumption()),
        leads_to(lift_state(a_state_pred()), lift_state(c_state_pred()))
    )
}

/// Proves `|= []next /\ WF(a_b) /\ WF(b_c) => (a ~> c)`

proof fn prove_a_leads_to_c()
    ensures
        valid(a_leads_to_c())
{
    assert forall |any_ex: Execution<SimpleState>| a_leads_to_c().satisfied_by(any_ex) by {
        if and(
            and(always(lift_action(next_action_pred())), weak_fairness(a_b_action_pred())),
            weak_fairness(b_c_action_pred())
        ).satisfied_by(any_ex) {
            prove_a_leads_to_b();
            assert(implies(
                and(always(lift_action(next_action_pred())), weak_fairness(a_b_action_pred())),
                leads_to(lift_state(a_state_pred()), lift_state(b_state_pred()))
            ).satisfied_by(any_ex));
            // assert(leads_to(lift_state(a_state_pred()), lift_state(b_state_pred())).satisfied_by(any_ex));

            prove_b_leads_to_c();
            assert(implies(
                and(always(lift_action(next_action_pred())), weak_fairness(b_c_action_pred())),
                leads_to(lift_state(b_state_pred()), lift_state(c_state_pred()))
            ).satisfied_by(any_ex));
            // assert(leads_to(lift_state(b_state_pred()), lift_state(c_state_pred())).satisfied_by(any_ex));

            leads_to_trans(a_state_pred(), b_state_pred(), c_state_pred());
            assert(implies(
                and(
                    leads_to(lift_state(a_state_pred()), lift_state(b_state_pred())),
                    leads_to(lift_state(b_state_pred()), lift_state(c_state_pred()))
                ),
                leads_to(lift_state(a_state_pred()), lift_state(c_state_pred()))
            ).satisfied_by(any_ex));
            // assert(leads_to(lift_state(a_state_pred()), lift_state(c_state_pred())).satisfied_by(any_ex));
        }
    };
}

spec fn eventually_c() -> TempPred<SimpleState> {
    implies(
        and(
            lift_state(init_state_pred()),
            and(always(lift_action(next_action_pred())), weak_fairness_assumption())
        ),
        eventually(lift_state(c_state_pred()))
    )
}

/// Proves `|= init /\ []next /\ WF(a_b) /\ WF(b_c) => <>c`

proof fn prove_eventually_c()
    ensures
        valid(eventually_c())
{
    assert forall |any_ex: Execution<SimpleState>| eventually_c().satisfied_by(any_ex) by {
        if and(
            lift_state(init_state_pred()),
            and(always(lift_action(next_action_pred())), weak_fairness_assumption())
        ).satisfied_by(any_ex) {
            prove_a_leads_to_c();
            assert(implies(
                and(always(lift_action(next_action_pred())), weak_fairness_assumption()),
                leads_to(lift_state(a_state_pred()), lift_state(c_state_pred()))
            ).satisfied_by(any_ex));
            // assert(leads_to(lift_state(a_state_pred()), lift_state(c_state_pred())).satisfied_by(any_ex));

            prove_init_a();
            // assert(lift_state(a_state_pred()).satisfied_by(any_ex));

            leads_to_apply(a_state_pred(), c_state_pred());
            assert(implies(
                and(
                    lift_state(a_state_pred()),
                    leads_to(lift_state(a_state_pred()), lift_state(c_state_pred()))
                ),
                eventually(lift_state(c_state_pred()))
            ).satisfied_by(any_ex));
            // assert(eventually(lift_state(c_state_pred())).satisfied_by(any_ex));
        }
    };
}

}
