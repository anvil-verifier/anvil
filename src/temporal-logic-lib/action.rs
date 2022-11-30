// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::{option::*, set::*};
use crate::temporal_logic::*;
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
}

#[is_variant]
pub enum ActionResult<State, Output> {
    Disabled,
    Enabled(State, Output)
}

/// `NetworkAction` helps to write network actions in a disciplined way
/// by explicitly writing `precondition` and `transition`.
///
/// It takes two generic types:
/// * `State`: The (internal) state of the network. For example, messages on the fly.
/// * `Message`: The message that the network receives and sends.
pub struct NetworkAction<#[verifier(maybe_negative)] State, #[verifier(maybe_negative)] Message> {
    /// The condition that enables the host action. For example, whether the delivered message was sent before.
    pub precondition: FnSpec(Option<Message>, State) -> bool,

    /// The new internal state made by the transition.
    pub transition: FnSpec(Option<Message>, State, Set<Message>) -> State,
}

#[is_variant]
pub enum NetworkActionResult<State> {
    Disabled,
    Enabled(State)
}

}
