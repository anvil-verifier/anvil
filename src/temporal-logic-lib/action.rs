// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::{option::*, set::*};
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

#[is_variant]
pub enum HostActionResult<State, Output> {
    Disabled,
    Enabled(State, Output)
}

/// `HostAction` helps to write host actions in a disciplined way
/// by explicitly writing `precondition`, `transition` and `output`.
///
/// It takes three generic types:
/// * `State`: The (internal) state of the host.
/// * `Input`: The input from the external world of the state machine. For example, a message.
/// * `Output`: The output to send to the external world of the state machine. For example, a set of messages.
pub struct HostAction<#[verifier(maybe_negative)] State, #[verifier(maybe_negative)] Input, #[verifier(maybe_negative)] Output> {
    /// The condition that enables the host action.
    pub precondition: FnSpec(Input, State) -> bool,

    /// The new internal state and output made by the transition.
    pub transition: FnSpec(Input, State) -> (State, Output),
}

#[is_variant]
pub enum NetworkActionResult<State> {
    Disabled,
    Enabled(State)
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

/// `NetworkAction` helps to write compound state machine actions in a disciplined way
/// by explicitly writing `precondition` and `transition`.
///
/// It takes two generic types:
/// * `State`: The state of the compound state machine.
/// * `Input`:The input selected by the compound state machine to feed to the host state machine.
pub struct CompoundAction<#[verifier(maybe_negative)] State, #[verifier(maybe_negative)] Input> {
    /// The condition that enables the host action.
    pub precondition: FnSpec(Input, State) -> bool,

    /// The new internal state and output made by the transition.
    pub transition: FnSpec(Input, State) -> State,
}

impl<State, Input> CompoundAction<State, Input> {
    pub open spec fn pred(self, input: Input) -> ActionPred<State> {
        |s: State, s_prime: State|{
            &&& (self.precondition)(input, s)
            &&& s_prime === (self.transition)(input, s)
        }
    }
}

}
