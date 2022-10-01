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

pub open spec fn x_is_a_as_set() -> Set<SimpleState> {
    Set::new(|state: SimpleState| state.x === ABC::A)
}

pub open spec fn x_is_b_as_set() -> Set<SimpleState> {
    Set::new(|state: SimpleState| state.x === ABC::B)
}

pub open spec fn x_is_c_as_set() -> Set<SimpleState> {
    Set::new(|state: SimpleState| state.x === ABC::C)
}

pub open spec fn a_leads_to_b() -> bool {
    valid(
        implies(
            and(
                always(lift_action(next_as_set())),
                weak_fairness(a_b_as_set())
            ),
            leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_b_as_set()))
        )
    )
}

proof fn prove_a_leads_to_b()
    ensures
        a_leads_to_b()
{
    assert forall |any_ex: Execution| lift_state(x_is_a_as_set()).contains(any_ex) ==> #[trigger] enabled(a_b_as_set()).contains(any_ex)
    by {
        if lift_state(x_is_a_as_set()).contains(any_ex) {
            let witness_s_prime = SimpleState {
                x: ABC::B,
                happy: any_ex[0].happy,
            };
            assert(witness_s_prime.x === ABC::B && witness_s_prime.happy === any_ex[0].happy);
            let s_prime: SimpleState = choose|s_prime: SimpleState| s_prime.x === ABC::B && s_prime.happy === any_ex[0].happy;
            let witness_action: Action = Action {
                state_0: any_ex[0],
                state_1: s_prime,
            };
            assert(a_b_as_set().contains(witness_action) && witness_action.state_0 === any_ex[0]);
        }
    };
    wf1(next_as_set(), a_b_as_set(), x_is_a_as_set(), x_is_b_as_set());
}

pub open spec fn init_a() -> bool {
    valid(
        implies(
            lift_state(init_as_set()),
            lift_state(x_is_a_as_set())
        )
    )
}

proof fn prove_init_a()
    ensures
        init_a()
{}


pub open spec fn eventually_b() -> bool {
    valid(
        implies(
            and(
                lift_state(init_as_set()),
                and(
                    always(lift_action(next_as_set())),
                    weak_fairness(a_b_as_set())
                )
            ),
            eventually(lift_state(x_is_b_as_set()))
        )
    )
}

proof fn prove_eventually_b()
    ensures
        eventually_b()
{
    assert forall |any_ex: Execution|
        any_ex.len() >= 2 ==> (
            #[trigger] lift_state(init_as_set()).contains(any_ex) && always(lift_action(next_as_set())).contains(any_ex) && weak_fairness(a_b_as_set()).contains(any_ex) ==>
                eventually(lift_state(x_is_b_as_set())).contains(any_ex)
        )
    by {
        if any_ex.len() >= 2 {
            if lift_state(init_as_set()).contains(any_ex) && always(lift_action(next_as_set())).contains(any_ex) && weak_fairness(a_b_as_set()).contains(any_ex) {
                prove_a_leads_to_b();
                assert(implies(and(always(lift_action(next_as_set())), weak_fairness(a_b_as_set())), leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_b_as_set()))).contains(any_ex));
                assert(leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_b_as_set())).contains(any_ex));

                prove_init_a();
                assert(lift_state(x_is_a_as_set()).contains(any_ex));

                leads_to_apply(x_is_a_as_set(), x_is_b_as_set());
                assert(implies(and(lift_state(x_is_a_as_set()), leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_b_as_set()))), eventually(lift_state(x_is_b_as_set()))).contains(any_ex));
                assert(eventually(lift_state(x_is_b_as_set())).contains(any_ex));
            }
        }
    }
}
pub open spec fn b_leads_to_c() -> bool {
    valid(
        implies(
            and(
                always(lift_action(next_as_set())),
                weak_fairness(b_c_as_set())
            ),
            leads_to(lift_state(x_is_b_as_set()), lift_state(x_is_c_as_set()))
        )
    )
}

proof fn prove_b_leads_to_c()
    ensures
        b_leads_to_c()
{
    assert forall |any_ex: Execution|
        any_ex.len() >= 2 ==> (
            lift_state(x_is_b_as_set()).contains(any_ex) ==> #[trigger] enabled(b_c_as_set()).contains(any_ex)
        )
    by {
        if any_ex.len() >= 2 {
            if lift_state(x_is_b_as_set()).contains(any_ex) {
                let witness_s_prime = SimpleState {
                    x: ABC::C,
                    happy: any_ex[0].happy,
                };
                assert(witness_s_prime.x === ABC::C && witness_s_prime.happy === any_ex[0].happy);
                let s_prime: SimpleState = choose|s_prime: SimpleState| s_prime.x === ABC::C && s_prime.happy === any_ex[0].happy;
                let witness_action: Action = Action {
                    state_0: any_ex[0],
                    state_1: s_prime,
                };
                assert(b_c_as_set().contains(witness_action) && witness_action.state_0 === any_ex[0]);
            }
        }
    };
    wf1(next_as_set(), b_c_as_set(), x_is_b_as_set(), x_is_c_as_set());
}

pub open spec fn a_leads_to_c() -> bool {
    valid(
        implies(
            and(
                always(lift_action(next_as_set())),
                and(
                    weak_fairness(a_b_as_set()),
                    weak_fairness(b_c_as_set())
                )
            ),
            leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_c_as_set()))
        )
    )
}

proof fn prove_a_leads_to_c()
    ensures
        a_leads_to_c()
{
    assert forall |any_ex: Execution|
        any_ex.len() >= 2 ==> (
            always(lift_action(next_as_set())).contains(any_ex) && #[trigger] weak_fairness(a_b_as_set()).contains(any_ex) && #[trigger] weak_fairness(b_c_as_set()).contains(any_ex) ==>
                leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_c_as_set())).contains(any_ex)
            )
    by {
        if any_ex.len() >= 2 {
            if always(lift_action(next_as_set())).contains(any_ex) {
                if weak_fairness(a_b_as_set()).contains(any_ex) {
                    if weak_fairness(b_c_as_set()).contains(any_ex) {
                        prove_a_leads_to_b();
                        assert(implies(and(always(lift_action(next_as_set())), weak_fairness(a_b_as_set())), leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_b_as_set()))).contains(any_ex));
                        assert(leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_b_as_set())).contains(any_ex));

                        prove_b_leads_to_c();
                        assert(implies(and(always(lift_action(next_as_set())), weak_fairness(b_c_as_set())), leads_to(lift_state(x_is_b_as_set()), lift_state(x_is_c_as_set()))).contains(any_ex));
                        assert(leads_to(lift_state(x_is_b_as_set()), lift_state(x_is_c_as_set())).contains(any_ex));

                        leads_to_trans(x_is_a_as_set(), x_is_b_as_set(), x_is_c_as_set());
                        assert(implies(and(leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_b_as_set())), leads_to(lift_state(x_is_b_as_set()), lift_state(x_is_c_as_set()))), leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_c_as_set()))).contains(any_ex));
                        assert(leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_c_as_set())).contains(any_ex));
                    }
                }
            }
        }

    };
}


pub open spec fn eventually_c() -> bool {
    valid(
        implies(
            and(
                lift_state(init_as_set()),
                and(
                    always(lift_action(next_as_set())),
                    and(
                        weak_fairness(a_b_as_set()),
                        weak_fairness(b_c_as_set())
                    )
                )
            ),
            eventually(lift_state(x_is_c_as_set()))
        )
    )
}

proof fn prove_eventually_c()
    ensures
        eventually_c()
{
    assert forall |any_ex: Execution|
        any_ex.len() >= 2 ==> (
            #[trigger] lift_state(init_as_set()).contains(any_ex) && always(lift_action(next_as_set())).contains(any_ex) && weak_fairness(a_b_as_set()).contains(any_ex) && weak_fairness(b_c_as_set()).contains(any_ex) ==>
                eventually(lift_state(x_is_c_as_set())).contains(any_ex)
        )
    by {
        if any_ex.len() >= 2 {
            if lift_state(init_as_set()).contains(any_ex) && always(lift_action(next_as_set())).contains(any_ex) && weak_fairness(a_b_as_set()).contains(any_ex) && weak_fairness(b_c_as_set()).contains(any_ex) {
                prove_a_leads_to_c();
                assert(implies(and(always(lift_action(next_as_set())), and(weak_fairness(a_b_as_set()), weak_fairness(b_c_as_set()))), leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_c_as_set()))).contains(any_ex));
                assert(leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_c_as_set())).contains(any_ex));

                prove_init_a();
                assert(lift_state(x_is_a_as_set()).contains(any_ex));

                leads_to_apply(x_is_a_as_set(), x_is_c_as_set());
                assert(implies(and(lift_state(x_is_a_as_set()), leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_c_as_set()))), eventually(lift_state(x_is_c_as_set()))).contains(any_ex));
                assert(eventually(lift_state(x_is_c_as_set())).contains(any_ex));
            }
        }
    }
}


}
