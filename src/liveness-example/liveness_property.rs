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

pub open spec fn x_is_a_as_set() -> StatePred {
    Set::new(|state: SimpleState| state.x === ABC::A)
}

pub open spec fn x_is_b_as_set() -> StatePred {
    Set::new(|state: SimpleState| state.x === ABC::B)
}

pub open spec fn x_is_c_as_set() -> StatePred {
    Set::new(|state: SimpleState| state.x === ABC::C)
}

pub open spec fn a_leads_to_b() -> TempPred {
    implies(and(always(lift_action(next_as_set())), weak_fairness(a_b_as_set())), leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_b_as_set())))
}

proof fn prove_a_leads_to_b()
    ensures
        valid(a_leads_to_b())
{
    assert forall |any_ex: Execution| implies(lift_state(x_is_a_as_set()), enabled(a_b_as_set())).contains(any_ex)
    by {
        if lift_state(x_is_a_as_set()).contains(any_ex) {
            // We need a witness to coax Verus that there exists a a_b() action that is enabled when x_is_a()
            let witness_action = Action {
                state: any_ex[0],
                state_prime: SimpleState {
                    x: ABC::B,
                    happy: any_ex[0].happy,
                }
            };
            assert(a_b_as_set().contains(witness_action) && witness_action.state === any_ex[0]);
        }
    };
    wf1(next_as_set(), a_b_as_set(), x_is_a_as_set(), x_is_b_as_set());
}

pub open spec fn init_a() -> TempPred {
    implies(lift_state(init_as_set()), lift_state(x_is_a_as_set()))
}

proof fn prove_init_a()
    ensures
        valid(init_a())
{}


pub open spec fn eventually_b() -> TempPred {
    implies(and(lift_state(init_as_set()), and(always(lift_action(next_as_set())), weak_fairness(a_b_as_set()))), eventually(lift_state(x_is_b_as_set())))
}

proof fn prove_eventually_b()
    ensures
        valid(eventually_b())
{
    assert forall |any_ex: Execution| eventually_b().contains(any_ex) by {
        if and(lift_state(init_as_set()), and(always(lift_action(next_as_set())), weak_fairness(a_b_as_set()))).contains(any_ex) {
            prove_a_leads_to_b();
            assert(implies(and(always(lift_action(next_as_set())), weak_fairness(a_b_as_set())), leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_b_as_set()))).contains(any_ex));
            // assert(leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_b_as_set())).contains(any_ex));

            prove_init_a();
            // assert(lift_state(x_is_a_as_set()).contains(any_ex));

            leads_to_apply(x_is_a_as_set(), x_is_b_as_set());
            assert(implies(and(lift_state(x_is_a_as_set()), leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_b_as_set()))), eventually(lift_state(x_is_b_as_set()))).contains(any_ex));
            // assert(eventually(lift_state(x_is_b_as_set())).contains(any_ex));
        }
    };
}

pub open spec fn b_leads_to_c() -> TempPred {
    implies(and(always(lift_action(next_as_set())), weak_fairness(b_c_as_set())), leads_to(lift_state(x_is_b_as_set()), lift_state(x_is_c_as_set())))
}

proof fn prove_b_leads_to_c()
    ensures
        valid(b_leads_to_c())
{
    assert forall |any_ex: Execution| implies(lift_state(x_is_b_as_set()), enabled(b_c_as_set())).contains(any_ex) by {
        if lift_state(x_is_b_as_set()).contains(any_ex) {
            // We need a witness to coax Verus that there exists a b_c() action that is enabled when x_is_b()
            let witness_action = Action {
                state: any_ex[0],
                state_prime: SimpleState {
                    x: ABC::C,
                    happy: any_ex[0].happy,
                }
            };
            assert(b_c_as_set().contains(witness_action) && witness_action.state === any_ex[0]);
        }
    };
    wf1(next_as_set(), b_c_as_set(), x_is_b_as_set(), x_is_c_as_set());
}

pub open spec fn a_leads_to_c() -> TempPred {
    implies(and(always(lift_action(next_as_set())), and(weak_fairness(a_b_as_set()), weak_fairness(b_c_as_set()))), leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_c_as_set())))
}

proof fn prove_a_leads_to_c()
    ensures
        valid(a_leads_to_c())
{
    assert forall |any_ex: Execution| a_leads_to_c().contains(any_ex) by {
        if and(and(always(lift_action(next_as_set())), weak_fairness(a_b_as_set())), weak_fairness(b_c_as_set())).contains(any_ex) {
            prove_a_leads_to_b();
            assert(implies(and(always(lift_action(next_as_set())), weak_fairness(a_b_as_set())), leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_b_as_set()))).contains(any_ex));
            // assert(leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_b_as_set())).contains(any_ex));

            prove_b_leads_to_c();
            assert(implies(and(always(lift_action(next_as_set())), weak_fairness(b_c_as_set())), leads_to(lift_state(x_is_b_as_set()), lift_state(x_is_c_as_set()))).contains(any_ex));
            // assert(leads_to(lift_state(x_is_b_as_set()), lift_state(x_is_c_as_set())).contains(any_ex));

            leads_to_trans(x_is_a_as_set(), x_is_b_as_set(), x_is_c_as_set());
            assert(implies(and(leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_b_as_set())), leads_to(lift_state(x_is_b_as_set()), lift_state(x_is_c_as_set()))), leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_c_as_set()))).contains(any_ex));
            // assert(leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_c_as_set())).contains(any_ex));
        }
    };
}


pub open spec fn eventually_c() -> TempPred {
    implies(and(lift_state(init_as_set()), and(always(lift_action(next_as_set())), and(weak_fairness(a_b_as_set()), weak_fairness(b_c_as_set())))), eventually(lift_state(x_is_c_as_set())))
}

proof fn prove_eventually_c()
    ensures
        valid(eventually_c())
{
    assert forall |any_ex: Execution| eventually_c().contains(any_ex) by {
        if and(lift_state(init_as_set()), and(always(lift_action(next_as_set())), and(weak_fairness(a_b_as_set()), weak_fairness(b_c_as_set())))).contains(any_ex) {
            prove_a_leads_to_c();
            assert(implies(and(always(lift_action(next_as_set())), and(weak_fairness(a_b_as_set()), weak_fairness(b_c_as_set()))), leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_c_as_set()))).contains(any_ex));
            // assert(leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_c_as_set())).contains(any_ex));

            prove_init_a();
            // assert(lift_state(x_is_a_as_set()).contains(any_ex));

            leads_to_apply(x_is_a_as_set(), x_is_c_as_set());
            assert(implies(and(lift_state(x_is_a_as_set()), leads_to(lift_state(x_is_a_as_set()), lift_state(x_is_c_as_set()))), eventually(lift_state(x_is_c_as_set()))).contains(any_ex));
            // assert(eventually(lift_state(x_is_c_as_set())).contains(any_ex));
        }
    };
}


}
