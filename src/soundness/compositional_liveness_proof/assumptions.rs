// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::soundness::compositional_liveness_proof::{properties::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub closed spec fn a_inv<S>() -> StatePred<S>;

pub closed spec fn b_inv<S>() -> StatePred<S>;

#[verifier(external_body)]
pub proof fn b_inv_holds_locally<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(init::<S>())),
        spec.entails(always(lift_action(next_with_b_only::<S, I>()))),
    ensures
        spec.entails(always(lift_state(b_inv::<S>()))),
{}

#[verifier(external_body)]
pub proof fn a_does_nothing_beyond_what_env_does<S, I>(input: I) -> (env_input: I)
    ensures forall |s, s_prime: S| #[trigger] controller_a_next(input)(s, s_prime)
            ==> environment_next(env_input)(s, s_prime)
{
    arbitrary()
}

#[verifier(external_body)]
pub proof fn b_property_holds_locally<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(init::<S>())),
        spec.entails(always(lift_action(next_with_b_only::<S, I>()))),
        spec.entails(fairness::<S>()),
        spec.entails(always(lift_state(a_inv::<S>()))),
    ensures
        spec.entails(b_property::<S>()),
{}

#[verifier(external_body)]
pub proof fn a_inv_holds_locally<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(init::<S>())),
        spec.entails(always(lift_action(next_with_a_only::<S, I>()))),
    ensures
        spec.entails(always(lift_state(a_inv::<S>()))),
{}

#[verifier(external_body)]
pub proof fn b_does_nothing_beyond_what_env_does<S, I>(input: I) -> (env_input: I)
    ensures forall |s, s_prime: S| #[trigger] controller_b_next(input)(s, s_prime)
            ==> environment_next(env_input)(s, s_prime)
{
    arbitrary()
}

#[verifier(external_body)]
pub proof fn a_property_holds_locally<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(init::<S>())),
        spec.entails(always(lift_action(next_with_a_only::<S, I>()))),
        spec.entails(fairness::<S>()),
        spec.entails(always(lift_state(b_inv::<S>()))),
        spec.entails(b_property::<S>()),
    ensures
        spec.entails(a_property::<S>()),
{}

}
