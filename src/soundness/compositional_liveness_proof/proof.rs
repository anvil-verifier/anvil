// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::soundness::compositional_liveness_proof::{
    assumptions::*, properties::*, state_machine::*,
};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

proof fn lower_liveness_holds_globally<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(init::<S>())),
        spec.entails(always(lift_action(next::<S, I>()))),
        spec.entails(fairness::<S>()),
    ensures
        spec.entails(lower_esr::<S>()),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(lift_action(next_without_lower::<S, I>())).satisfied_by(ex) by {
        assert(spec.implies(always(lift_action(next::<S, I>()))).satisfied_by(ex));
        assert forall |i| #[trigger] lift_action(next_without_lower::<S, I>()).satisfied_by(ex.suffix(i)) by {
            assert(lift_action(next::<S, I>()).satisfied_by(ex.suffix(i)));
            next_does_nothing_beyond_next_without_lower::<S, I>(ex.suffix(i).head(), ex.suffix(i).head_next());
        }
    }

    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(lift_action(next_without_upper::<S, I>())).satisfied_by(ex) by {
        assert(spec.implies(always(lift_action(next::<S, I>()))).satisfied_by(ex));
        assert forall |i| #[trigger] lift_action(next_without_upper::<S, I>()).satisfied_by(ex.suffix(i)) by {
            assert(lift_action(next::<S, I>()).satisfied_by(ex.suffix(i)));
            next_does_nothing_beyond_next_without_upper::<S, I>(ex.suffix(i).head(), ex.suffix(i).head_next());
        }
    }

    upper_inv_holds_locally::<S, I>(spec);
    lower_liveness_holds_locally::<S, I>(spec);
}

proof fn upper_liveness_holds_globally<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(init::<S>())),
        spec.entails(always(lift_action(next::<S, I>()))),
        spec.entails(fairness::<S>()),
        spec.entails(lower_esr::<S>()),
    ensures
        spec.entails(upper_esr::<S>()),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(lift_action(next_without_lower::<S, I>())).satisfied_by(ex) by {
        assert(spec.implies(always(lift_action(next::<S, I>()))).satisfied_by(ex));
        assert forall |i| #[trigger] lift_action(next_without_lower::<S, I>()).satisfied_by(ex.suffix(i)) by {
            assert(lift_action(next::<S, I>()).satisfied_by(ex.suffix(i)));
            next_does_nothing_beyond_next_without_lower::<S, I>(ex.suffix(i).head(), ex.suffix(i).head_next());
        }
    }

    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(lift_action(next_without_upper::<S, I>())).satisfied_by(ex) by {
        assert(spec.implies(always(lift_action(next::<S, I>()))).satisfied_by(ex));
        assert forall |i| #[trigger] lift_action(next_without_upper::<S, I>()).satisfied_by(ex.suffix(i)) by {
            assert(lift_action(next::<S, I>()).satisfied_by(ex.suffix(i)));
            next_does_nothing_beyond_next_without_upper::<S, I>(ex.suffix(i).head(), ex.suffix(i).head_next());
        }
    }

    lower_liveness_holds_globally::<S, I>(spec);
    lower_inv_holds_locally::<S, I>(spec);
    upper_liveness_holds_locally::<S, I>(spec);
}

proof fn next_does_nothing_beyond_next_without_lower<S, I>(s: S, s_prime: S)
    requires
        next::<S, I>()(s, s_prime),
    ensures
       next_without_lower::<S, I>()(s, s_prime),
{
    let step = choose |step: Step<I>| next_step(s, s_prime, step);
    assert(next_step(s, s_prime, step));
    match step {
        Step::LowerControllerStep(input) => {
            let env_input = lower_does_nothing_beyond_what_env_does::<S, I>(input);
            assert(next_without_lower_step(s, s_prime, Step::EnvStep(env_input)));
        }
        _ => {
            assert(next_without_lower_step(s, s_prime, step));
        }
    }
}

proof fn next_does_nothing_beyond_next_without_upper<S, I>(s: S, s_prime: S)
    requires
        next::<S, I>()(s, s_prime),
    ensures
       next_without_upper::<S, I>()(s, s_prime),
{
    let step = choose |step: Step<I>| next_step(s, s_prime, step);
    assert(next_step(s, s_prime, step));
    match step {
        Step::UpperControllerStep(input) => {
            let env_input = upper_does_nothing_beyond_what_env_does::<S, I>(input);
            assert(next_without_upper_step(s, s_prime, Step::EnvStep(env_input)));
        }
        _ => {
            assert(next_without_upper_step(s, s_prime, step));
        }
    }
}

}
