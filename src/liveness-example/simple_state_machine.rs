// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::set::*;
use crate::state::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn init(s: State) -> bool {
    &&& s.x === ABC::A
    &&& s.happy
}

pub open spec fn a_b(s: State, s_prime: State) -> bool {
    &&& s.x === ABC::A
    &&& s_prime.x === ABC::B
    &&& s.happy === s_prime.happy
}


pub open spec fn b_c(s: State, s_prime: State) -> bool {
    &&& s.x === ABC::B
    &&& s_prime.x === ABC::C
    &&& s.happy === s_prime.happy
}

pub open spec fn stutter(s: State, s_prime: State) -> bool {
    s === s_prime
}

pub open spec fn next(s: State, s_prime: State) -> bool {
    ||| a_b(s, s_prime)
    ||| b_c(s, s_prime)
    ||| stutter(s, s_prime)
}

pub open spec fn init_state_pred() -> StatePred {
    StatePred::new(|state: State| init(state))
}

pub open spec fn a_b_action_pred() -> ActionPred {
    ActionPred::new(|action: Action| a_b(action.state, action.state_prime))
}

pub open spec fn b_c_action_pred() -> ActionPred {
    ActionPred::new(|action: Action| b_c(action.state, action.state_prime))
}

pub open spec fn stutter_action_pred() -> ActionPred {
    ActionPred::new(|action: Action| stutter(action.state, action.state_prime))
}

pub open spec fn next_action_pred() -> ActionPred {
    ActionPred::new(|action: Action| next(action.state, action.state_prime))
}

}
