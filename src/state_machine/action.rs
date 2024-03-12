// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

#[verifier(reject_recursive_types(State))]
#[verifier(reject_recursive_types(Input))]
#[verifier(reject_recursive_types(Output))]
pub struct Action<State, Input, Output> {
    /// The condition that enables the host action.
    pub precondition: spec_fn(Input, State) -> bool,

    /// The new internal state and output made by the transition.
    pub transition: spec_fn(Input, State) -> (State, Output),
}

impl<State, Input, Output> Action<State, Input, Output> {
    pub open spec fn pre(self, input: Input) -> StatePred<State> {
        |s: State| (self.precondition)(input, s)
    }

    pub open spec fn forward(self, input: Input) -> ActionPred<State> {
        |s: State, s_prime: State| {
            &&& (self.precondition)(input, s)
            &&& s_prime == (self.transition)(input, s).0
        }
    }

    /// `weak_fairness` assumption says that,
    /// it is always true that, if `pre` is always true, `forward` eventually becomes true
    pub open spec fn weak_fairness(self, input: Input) -> TempPred<State> {
        always(lift_state(self.pre(input))).leads_to(lift_action(self.forward(input)))
    }

    /// `wf1` is a specialized version of temporal_logic_rules::wf1 for Action
    pub proof fn wf1(self, input: Input, spec: TempPred<State>, next: ActionPred<State>, pre: StatePred<State>, post: StatePred<State>)
        requires
            forall |s, s_prime: State| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
            forall |s, s_prime: State| pre(s) && #[trigger] next(s, s_prime) && self.forward(input)(s, s_prime) ==> post(s_prime),
            spec.entails(always(lift_action(next))),
            spec.entails(always(lift_state(pre).implies(lift_state(self.pre(input))))),
            spec.entails(self.weak_fairness(input)),
        ensures spec.entails(lift_state(pre).leads_to(lift_state(post))),
    {
        always_implies_preserved_by_always_temp::<State>(spec, lift_state(pre), lift_state(self.pre(input)));
        leads_to_weaken_temp::<State>(spec, always(lift_state(self.pre(input))), lift_action(self.forward(input)), always(lift_state(pre)), lift_action(self.forward(input)));
        wf1_variant_temp::<State>(spec, lift_action(next), lift_action(self.forward(input)), lift_state(pre), lift_state(post));
    }

    /// `wf1_borrow_from_spec` is a specialized version of temporal_logic_rules::wf1 for Action
    pub proof fn wf1_borrow_from_spec(self, input: Input, spec: TempPred<State>, next: ActionPred<State>, c: StatePred<State>, pre: StatePred<State>, post: StatePred<State>)
        requires
            forall |s, s_prime: State| pre(s) && c(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
            forall |s, s_prime: State| pre(s) && c(s) && #[trigger] next(s, s_prime) && self.forward(input)(s, s_prime) ==> post(s_prime),
            spec.entails(always(lift_action(next))),
            spec.entails(always((lift_state(pre).and(lift_state(c))).implies(lift_state(self.pre(input))))),
            spec.entails(self.weak_fairness(input)),
            spec.entails(always(lift_state(c))),
        ensures spec.entails(lift_state(pre).leads_to(lift_state(post))),
    {
        always_implies_preserved_by_always_temp::<State>(spec, lift_state(pre).and(lift_state(c)), lift_state(self.pre(input)));
        leads_to_weaken_temp::<State>(spec, always(lift_state(self.pre(input))), lift_action(self.forward(input)), always(lift_state(pre).and(lift_state(c))), lift_action(self.forward(input)));
        wf1_variant_borrow_from_spec_temp::<State>(spec, lift_action(next), lift_action(self.forward(input)), lift_state(c), lift_state(pre), lift_state(post));
    }
}

#[is_variant]
pub enum ActionResult<State, Output> {
    Disabled,
    Enabled(State, Output)
}

}
