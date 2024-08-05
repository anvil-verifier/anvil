// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

// init function of the state machine
pub closed spec fn init<S>() -> StatePred<S>;

// next step action of the environment
pub closed spec fn environment_next<S, I>(input: I) -> ActionPred<S>;

// next step action of controller a
pub closed spec fn controller_a_next<S, I>(input: I) -> ActionPred<S>;

// next step action of controller b
pub closed spec fn controller_b_next<S, I>(input: I) -> ActionPred<S>;

// stutter step action to make always(next) hold
pub open spec fn stutter<S>() -> ActionPred<S> {
    |s, s_prime: S| s == s_prime
}

// Step decides which host to take a step and the input to that step
pub enum Step<I> {
    EnvStep(I),
    ControllerAStep(I),
    ControllerBStep(I),
    StutterStep(),
}

// next step action of the *global* cluster including env, a and b
pub open spec fn next<S, I>() -> ActionPred<S> {
    |s, s_prime: S| exists |step: Step<I>| #[trigger] next_step(s, s_prime, step)
}

pub open spec fn next_step<S, I>(s: S, s_prime: S, step: Step<I>) -> bool {
    match step {
        Step::EnvStep(input) => environment_next(input)(s, s_prime),
        Step::ControllerAStep(input) => controller_a_next(input)(s, s_prime),
        Step::ControllerBStep(input) => controller_b_next(input)(s, s_prime),
        Step::StutterStep() => stutter()(s, s_prime),
    }
}

// next step action of the *local* cluster including env and b
pub open spec fn next_with_b_only<S, I>() -> ActionPred<S> {
    |s, s_prime: S| exists |step: Step<I>| #[trigger] next_step_with_b_only(s, s_prime, step)
}

pub open spec fn next_step_with_b_only<S, I>(s: S, s_prime: S, step: Step<I>) -> bool {
    match step {
        Step::EnvStep(input) => environment_next(input)(s, s_prime),
        Step::ControllerAStep(input) => environment_next(input)(s, s_prime),
        Step::ControllerBStep(input) => controller_b_next(input)(s, s_prime),
        Step::StutterStep() => stutter()(s, s_prime),
    }
}

// next step action of the *local* cluster including env and a
pub open spec fn next_with_a_only<S, I>() -> ActionPred<S> {
    |s, s_prime: S| exists |step: Step<I>| #[trigger] next_step_with_a_only(s, s_prime, step)
}

pub open spec fn next_step_with_a_only<S, I>(s: S, s_prime: S, step: Step<I>) -> bool {
    match step {
        Step::EnvStep(input) => environment_next(input)(s, s_prime),
        Step::ControllerAStep(input) => controller_a_next(input)(s, s_prime),
        Step::ControllerBStep(input) => environment_next(input)(s, s_prime),
        Step::StutterStep() => stutter()(s, s_prime),
    }
}

// fairness condition that is needed for liveness
pub closed spec fn fairness<S>() -> TempPred<S>;

}
