// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub enum ABC {
    A,
    B,
    C,
}

pub struct SimpleState {
    pub x: ABC,
    pub happy: bool,
}

pub open spec fn init() -> StatePred<SimpleState> {
    |s: SimpleState| {
        &&& s.x === ABC::A
        &&& s.happy
    }
}

pub open spec fn a_b_pre() -> StatePred<SimpleState> {
    |s: SimpleState| s.x === ABC::A
}

pub open spec fn a_b() -> ActionPred<SimpleState> {
    |s, s_prime: SimpleState| {
        &&& a_b_pre()(s)
        &&& s_prime === SimpleState{
            x: ABC::B,
            happy: s.happy
        }
    }
}


pub open spec fn b_c_pre() -> StatePred<SimpleState> {
    |s: SimpleState| s.x === ABC::B
}

pub open spec fn b_c() -> ActionPred<SimpleState> {
    |s, s_prime: SimpleState| {
        &&& b_c_pre()(s)
        &&& s_prime === SimpleState{
            x: ABC::C,
            happy: s.happy
        }
    }
}

pub open spec fn stutter() -> ActionPred<SimpleState> {
    |s, s_prime: SimpleState| s === s_prime
}

pub open spec fn next() -> ActionPred<SimpleState> {
    |s, s_prime: SimpleState| {
        ||| a_b()(s, s_prime)
        ||| b_c()(s, s_prime)
        ||| stutter()(s, s_prime)
    }
}

pub open spec fn sm_spec() -> TempPred<SimpleState> {
    lift_state(init())
    .and(always(lift_action(next())))
    .and(weak_fairness(a_b()))
    .and(weak_fairness(b_c()))
}

pub proof fn a_b_enabled()
    ensures
        forall |s: SimpleState| #[trigger] state_pred_call(a_b_pre(), s) ==> enabled(a_b())(s),
{
    assert forall |s: SimpleState| #[trigger] state_pred_call(a_b_pre(), s) implies enabled(a_b())(s) by {
        let witness_s_prime = SimpleState {
            x: ABC::B,
            happy: s.happy,
        };
        assert(action_pred_call(a_b(), s, witness_s_prime));
    };
}

pub proof fn b_c_enabled()
    ensures
        forall |s: SimpleState| #[trigger] state_pred_call(b_c_pre(), s) ==> enabled(b_c())(s),
{
    assert forall |s: SimpleState| #[trigger] state_pred_call(b_c_pre(), s) implies enabled(b_c())(s) by {
        let witness_s_prime = SimpleState {
            x: ABC::C,
            happy: s.happy,
        };
        assert(action_pred_call(b_c(), s, witness_s_prime));
    };
}

}
