// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub closed spec fn init<S>() -> StatePred<S>;

pub closed spec fn environment_next<S, I>(input: I) -> ActionPred<S>;

pub closed spec fn upper_controller_next<S, I>(input: I) -> ActionPred<S>;

pub closed spec fn lower_controller_next<S, I>(input: I) -> ActionPred<S>;

pub open spec fn stutter<S>() -> ActionPred<S> {
    |s, s_prime: S| s == s_prime
}

pub enum Step<I> {
    EnvStep(I),
    UpperControllerStep(I),
    LowerControllerStep(I),
    StutterStep(),
}

pub closed spec fn dummy<I>(s: Step<I>) -> bool;

pub open spec fn next_step<S, I>(s: S, s_prime: S, step: Step<I>) -> bool {
    match step {
        Step::EnvStep(input) => environment_next(input)(s, s_prime),
        Step::UpperControllerStep(input) => upper_controller_next(input)(s, s_prime),
        Step::LowerControllerStep(input) => lower_controller_next(input)(s, s_prime),
        Step::StutterStep() => stutter()(s, s_prime),
    }
}

pub open spec fn next<S, I>() -> ActionPred<S> {
    |s, s_prime: S| exists |step: Step<I>| #[trigger] next_step(s, s_prime, step)
}

pub open spec fn next_without_upper_step<S, I>(s: S, s_prime: S, step: Step<I>) -> bool {
    match step {
        Step::EnvStep(input) => environment_next(input)(s, s_prime),
        Step::UpperControllerStep(input) => environment_next(input)(s, s_prime),
        Step::LowerControllerStep(input) => lower_controller_next(input)(s, s_prime),
        Step::StutterStep() => stutter()(s, s_prime),
    }
}

pub open spec fn next_without_upper<S, I>() -> ActionPred<S> {
    |s, s_prime: S| exists |step: Step<I>| #[trigger] next_without_upper_step(s, s_prime, step)
}

pub open spec fn next_without_lower_step<S, I>(s: S, s_prime: S, step: Step<I>) -> bool {
    match step {
        Step::EnvStep(input) => environment_next(input)(s, s_prime),
        Step::UpperControllerStep(input) => upper_controller_next(input)(s, s_prime),
        Step::LowerControllerStep(input) => environment_next(input)(s, s_prime),
        Step::StutterStep() => stutter()(s, s_prime),
    }
}

pub open spec fn next_without_lower<S, I>() -> ActionPred<S> {
    |s, s_prime: S| exists |step: Step<I>| #[trigger] next_without_lower_step(s, s_prime, step)
}


pub closed spec fn fairness<S>() -> TempPred<S>;

}
