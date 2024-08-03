// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::soundness::compositional_liveness_proof::{properties::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub closed spec fn upper_inv<S>() -> StatePred<S>;

pub closed spec fn lower_inv<S>() -> StatePred<S>;

#[verifier(external_body)]
pub proof fn lower_inv_holds_locally<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(init::<S>())),
        spec.entails(always(lift_action(next_without_upper::<S, I>()))),
    ensures
        spec.entails(always(lift_state(lower_inv::<S>()))),
{}

#[verifier(external_body)]
pub proof fn upper_does_nothing_beyond_what_env_does<S, I>(input: I) -> (env_input: I)
    ensures forall |s, s_prime: S| #[trigger] upper_controller_next(input)(s, s_prime)
            ==> environment_next(env_input)(s, s_prime)
{
    arbitrary()
}

#[verifier(external_body)]
pub proof fn lower_liveness_holds_locally<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(init::<S>())),
        spec.entails(always(lift_action(next_without_upper::<S, I>()))),
        spec.entails(fairness::<S>()),
        spec.entails(always(lift_state(upper_inv::<S>()))),
    ensures
        spec.entails(lower_esr::<S>()),
{}

#[verifier(external_body)]
pub proof fn upper_inv_holds_locally<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(init::<S>())),
        spec.entails(always(lift_action(next_without_lower::<S, I>()))),
    ensures
        spec.entails(always(lift_state(upper_inv::<S>()))),
{}

#[verifier(external_body)]
pub proof fn lower_does_nothing_beyond_what_env_does<S, I>(input: I) -> (env_input: I)
    ensures forall |s, s_prime: S| #[trigger] lower_controller_next(input)(s, s_prime)
            ==> environment_next(env_input)(s, s_prime)
{
    arbitrary()
}

#[verifier(external_body)]
pub proof fn upper_liveness_holds_locally<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(init::<S>())),
        spec.entails(always(lift_action(next_without_lower::<S, I>()))),
        spec.entails(fairness::<S>()),
        spec.entails(always(lift_state(lower_inv::<S>()))),
        spec.entails(lower_esr::<S>()),
    ensures
        spec.entails(upper_esr::<S>()),
{}

}
