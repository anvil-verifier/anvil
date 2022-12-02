// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::{option::*, set::*};
use crate::temporal_logic::*;
use crate::temporal_logic_rules;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct Action<#[verifier(maybe_negative)] State, #[verifier(maybe_negative)] Input, #[verifier(maybe_negative)] Output> {
    /// The condition that enables the host action.
    pub precondition: FnSpec(Input, State) -> bool,

    /// The new internal state and output made by the transition.
    pub transition: FnSpec(Input, State) -> (State, Output),
}

impl<State, Input, Output> Action<State, Input, Output> {
    pub open spec fn pre(self, input: Input) -> StatePred<State> {
        |s: State| (self.precondition)(input, s)
    }

    pub open spec fn forward(self, input: Input) -> ActionPred<State> {
        |s: State, s_prime: State| {
            &&& (self.precondition)(input, s)
            &&& s_prime === (self.transition)(input, s).0
        }
    }

    /// TODO: Write weak fairness assumptions with this method
    pub open spec fn weak_fairness(self, input: Input) -> TempPred<State> {
        always(lift_state(self.pre(input))).leads_to(lift_action(self.forward(input)))
    }

    /// `pre_implies_forward_enabled` gives a generic proof showing that
    /// if the precondition of a action is satisfied, the action is enabled
    pub proof fn pre_implies_forward_enabled(self, input: Input)
        ensures
            forall |s| state_pred_call(self.pre(input), s) ==> enabled(self.forward(input))(s),
    {
        assert forall |s| state_pred_call(self.pre(input), s) implies enabled(self.forward(input))(s) by {
            let s_prime = (self.transition)(input, s).0;
            assert(action_pred_call(self.forward(input), s, s_prime));
        };
    }

    /// `wf1` is a specialized version of temporal_logic_rules::wf1 for Action
    pub proof fn wf1(self, input: Input, spec: TempPred<State>, next: ActionPred<State>, post: StatePred<State>)
        requires
            forall |s, s_prime: State| self.pre(input)(s) && action_pred_call(next, s, s_prime) ==> self.pre(input)(s_prime) || post(s_prime),
            forall |s, s_prime: State| self.pre(input)(s) && action_pred_call(next, s, s_prime) && self.forward(input)(s, s_prime) ==> post(s_prime),
            spec.entails(always(lift_action(next))),
            spec.entails(weak_fairness(self.forward(input))),
        ensures
            spec.entails(lift_state(self.pre(input)).leads_to(lift_state(post))),
    {
        self.pre_implies_forward_enabled(input);
        temporal_logic_rules::wf1::<State>(spec, next, self.forward(input), self.pre(input), post);
    }
}

#[is_variant]
pub enum ActionResult<State, Output> {
    Disabled,
    Enabled(State, Output)
}

}
