// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::set::*;
use crate::state::*;
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

pub open spec fn init_as_set() -> StatePred {
    Set::new(|state: SimpleState| init(state))
}

pub open spec fn a_b_as_set() -> ActionPred {
    Set::new(|action: Action| a_b(action.state_0, action.state_1))
}

pub open spec fn b_c_as_set() -> ActionPred {
    Set::new(|action: Action| b_c(action.state_0, action.state_1))
}

pub open spec fn stutter_as_set() -> ActionPred {
    Set::new(|action: Action| stutter(action.state_0, action.state_1))
}

pub open spec fn next_as_set() -> ActionPred {
    Set::new(|action: Action| next(action.state_0, action.state_1))
}

}
