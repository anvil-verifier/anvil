// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pred::*;
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

pub open spec fn init(s: SimpleState) -> bool {
    &&& s.x === ABC::A
    &&& s.happy
}

pub open spec fn a_b(s: SimpleState, s_prime: SimpleState) -> bool {
    &&& s.x === ABC::A
    &&& s_prime.x === ABC::B
    &&& s.happy === s_prime.happy
}


pub open spec fn b_c(s: SimpleState, s_prime: SimpleState) -> bool {
    &&& s.x === ABC::B
    &&& s_prime.x === ABC::C
    &&& s.happy === s_prime.happy
}

pub open spec fn stutter(s: SimpleState, s_prime: SimpleState) -> bool {
    s === s_prime
}

pub open spec fn next(s: SimpleState, s_prime: SimpleState) -> bool {
    ||| a_b(s, s_prime)
    ||| b_c(s, s_prime)
    ||| stutter(s, s_prime)
}

pub open spec fn init_state_pred() -> StatePred<SimpleState> {
    StatePred::new(|state: SimpleState| init(state))
}

pub open spec fn a_b_action_pred() -> ActionPred<SimpleState> {
    ActionPred::new(|action: Action<SimpleState>| a_b(action.state, action.state_prime))
}

pub open spec fn b_c_action_pred() -> ActionPred<SimpleState> {
    ActionPred::new(|action: Action<SimpleState>| b_c(action.state, action.state_prime))
}

pub open spec fn stutter_action_pred() -> ActionPred<SimpleState> {
    ActionPred::new(|action: Action<SimpleState>| stutter(action.state, action.state_prime))
}

pub open spec fn next_action_pred() -> ActionPred<SimpleState> {
    ActionPred::new(|action: Action<SimpleState>| next(action.state, action.state_prime))
}

pub open spec fn sm_spec() -> TempPred<SimpleState> {
    and(
        init_state_pred().lift(),
        and(
            always(next_action_pred().lift()),
            and(weak_fairness(a_b_action_pred()), weak_fairness(b_c_action_pred()))
        )
    )
}

}
