// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::seq::*;
use crate::pervasive::set::*;
use crate::pervasive::set_lib::*;
use crate::simple_state_machine::*;
use crate::state::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn a_state_pred() -> StatePred {
    Set::new(|state: SimpleState| state.x === ABC::A)
}

pub open spec fn b_state_pred() -> StatePred {
    Set::new(|state: SimpleState| state.x === ABC::B)
}

pub open spec fn c_state_pred() -> StatePred {
    Set::new(|state: SimpleState| state.x === ABC::C)
}

pub open spec fn a_leads_to_b() -> TempPred {
    implies(and(always(lift_action(next_action_pred())), weak_fairness(a_b_action_pred())), leads_to(a_state_pred(), b_state_pred()))
}

// a boilerplate we'd like to disappear using syntax that expresses the primed state of actions
// functionally.
proof fn a_b_enabled()
    ensures enabled(a_b_action_pred()) === Set::new(|s: SimpleState| s.x === ABC::A)
{
    assert_sets_equal!( enabled(a_b_action_pred()), Set::new(|s: SimpleState| s.x === ABC::A),
        s => {
            if s.x === ABC::A {
                let witness_action = Action {
                    state: s,
                    state_prime: SimpleState { x: ABC::B, happy: s.happy, }
                };
                assert(a_b_action_pred().contains(witness_action));
            }
        }
    );
}

proof fn prove_a_leads_to_b()
    ensures
        valid(a_leads_to_b())
{
    a_b_enabled();
    wf1(next_action_pred(), a_b_action_pred(), a_state_pred(), b_state_pred());
}

pub open spec fn init_a() -> TempPred {
    implies(lift_state(init_state_pred()), lift_state(a_state_pred()))
}

proof fn prove_init_a()
    ensures
        valid(init_a())
{}

pub open spec fn eventually_b() -> TempPred {
    implies(
        smspec(),
        eventually(lift_state(b_state_pred()))
    )
}

// spec: the "context" of the assertion; assumed to be valid
// pred: the TempPred we expect to prove
// This is really just shorthand for a common boilerplate pattern in bisection-debugging a proof.
proof fn assert_pred(spec: TempPred, pred: TempPred)
    requires valid(implies(spec, pred))
    ensures valid(implies(spec, pred))
{
}

proof fn prove_eventually_b()
    ensures
        valid(eventually_b())
{
    apply_implies_auto();

    //prove_a_leads_to_b();
    //leads_to_apply(a_state_pred(), b_state_pred());

    // the "hard" precondition of make_leadsto_from_wf was showing a implies enabled(a_b_action),
    // which is only hard because enabled means showing an exists witness. Here ya go.
    a_b_enabled();

    // working backwards, "Oh! I'm trying to get a leadsto. This is the way to construct them."
    make_leadsto_from_wf(a_b_action_pred(), next_action_pred(), a_state_pred(), b_state_pred());

    assert_pred(smspec(),
        leads_to(a_state_pred(), b_state_pred())
    );

    leads_to_apply(a_state_pred(), b_state_pred());

//    assert(valid(implies(
//        smspec(),
//        eventually(lift_state(b_state_pred()))
//    )));
//    assert(valid(eventually_b()));
}

pub open spec fn b_leads_to_c() -> TempPred {
    implies(and(always(lift_action(next_action_pred())), weak_fairness(b_c_action_pred())), leads_to(b_state_pred(), c_state_pred()))
}

proof fn prove_b_leads_to_c()
    ensures
        valid(b_leads_to_c())
{
    assert forall |any_ex: Execution| implies(lift_state(b_state_pred()), tla_enabled(b_c_action_pred())).contains(any_ex) by {
        if lift_state(b_state_pred()).contains(any_ex) {
            // We need a witness to coax Verus that there exists a b_c() action that is enabled when x_is_b()
            let witness_action = Action {
                state: any_ex[0],
                state_prime: SimpleState {
                    x: ABC::C,
                    happy: any_ex[0].happy,
                }
            };
            assert(b_c_action_pred().contains(witness_action) && witness_action.state === any_ex[0]);
        }
    };
    wf1(next_action_pred(), b_c_action_pred(), b_state_pred(), c_state_pred());
}

pub open spec fn a_leads_to_c() -> TempPred {
    implies(and(always(lift_action(next_action_pred())), and(weak_fairness(a_b_action_pred()), weak_fairness(b_c_action_pred()))), leads_to(a_state_pred(), c_state_pred()))
}

proof fn prove_a_leads_to_c()
    ensures
        valid(a_leads_to_c())
{
    assert forall |any_ex: Execution| a_leads_to_c().contains(any_ex) by {
        if and(and(always(lift_action(next_action_pred())), weak_fairness(a_b_action_pred())), weak_fairness(b_c_action_pred())).contains(any_ex) {
            prove_a_leads_to_b();
            assert(implies(and(always(lift_action(next_action_pred())), weak_fairness(a_b_action_pred())), leads_to(a_state_pred(), b_state_pred())).contains(any_ex));

            prove_b_leads_to_c();
            assert(implies(and(always(lift_action(next_action_pred())), weak_fairness(b_c_action_pred())), leads_to(b_state_pred(), c_state_pred())).contains(any_ex));

            leads_to_trans(a_state_pred(), b_state_pred(), c_state_pred());
            assert(implies(and(leads_to(a_state_pred(), b_state_pred()), leads_to(b_state_pred(), c_state_pred())), leads_to(a_state_pred(), c_state_pred())).contains(any_ex));
        }
    };
}

pub open spec fn eventually_c() -> TempPred {
    implies(and(lift_state(init_state_pred()), and(always(lift_action(next_action_pred())), and(weak_fairness(a_b_action_pred()), weak_fairness(b_c_action_pred())))), eventually(lift_state(c_state_pred())))
}

proof fn prove_eventually_c()
    ensures
        valid(eventually_c())
{
    assert forall |any_ex: Execution| eventually_c().contains(any_ex) by {
        if and(lift_state(init_state_pred()), and(always(lift_action(next_action_pred())), and(weak_fairness(a_b_action_pred()), weak_fairness(b_c_action_pred())))).contains(any_ex) {
            prove_a_leads_to_c();
            assert(implies(and(always(lift_action(next_action_pred())), and(weak_fairness(a_b_action_pred()), weak_fairness(b_c_action_pred()))), leads_to(a_state_pred(), c_state_pred())).contains(any_ex));
            // assert(leads_to(lift_state(a_state_pred()), lift_state(c_state_pred())).contains(any_ex));

            prove_init_a();
            // assert(lift_state(a_state_pred()).contains(any_ex));

            leads_to_apply(a_state_pred(), c_state_pred());
            assert(implies(and(lift_state(a_state_pred()), leads_to(a_state_pred(), c_state_pred())), eventually(lift_state(c_state_pred()))).contains(any_ex));
            // assert(eventually(lift_state(c_state_pred())).contains(any_ex));
        }
    };
}


}
