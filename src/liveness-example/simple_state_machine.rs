// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::set::*;
use crate::state::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

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

pub open spec fn init_state_pred() -> StatePred {
    Set::new(|state: SimpleState| init(state))
}

pub open spec fn a_b_action_pred() -> ActionPred {
    Set::new(|action: Action| a_b(action.state, action.state_prime))
}

pub open spec fn b_c_action_pred() -> ActionPred {
    Set::new(|action: Action| b_c(action.state, action.state_prime))
}

pub open spec fn stutter_action_pred() -> ActionPred {
    Set::new(|action: Action| stutter(action.state, action.state_prime))
}

pub open spec fn next_action_pred() -> ActionPred {
    Set::new(|action: Action| next(action.state, action.state_prime))
}

// TODO(tej&jonh): generalize temporal_logic to simple_state_machine
pub open spec fn smspec() -> TempPred {
    and(
        lift_state(init_state_pred()),
        and(always(lift_action(next_action_pred())),
            weak_fairness(a_b_action_pred())))
}

}
