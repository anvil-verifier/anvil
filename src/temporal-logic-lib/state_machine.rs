// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::pervasive::{option::*, set::*};
use builtin::*;
use builtin_macros::*;

verus! {


/// `StateMachine` helps to write host state machines in a disciplined way
/// by explicitly writing `init`, `actions`, `step_to_action`, and `action_input`.
///
/// It takes four generic types:
/// * `State`: The (internal) state of the host.
/// * `Input`: The input from the external world of the state machine. For example a message.
/// * `ActionInput`: The input to feed to the action. It might be a compound of `Input` and other types.
/// * `Output`: The output to send to the external world of the state machine. For example a set of messages.
/// * `Step`: The step binding variable that the state machine chooses to decide the action.
pub struct StateMachine <
    #[verifier(maybe_negative)] State,
    #[verifier(maybe_negative)] Input,
    #[verifier(maybe_negative)] ActionInput,
    #[verifier(maybe_negative)] Output,
    #[verifier(maybe_negative)] Step,
> {
    /// Check if it is the initial internal state.
    pub init: FnSpec(State) -> bool,

    /// The set of actions the state machine can take.
    pub actions: Set<Action<State, ActionInput, Output>>,

    /// Return the corresponding action of the binding step.
    pub step_to_action: FnSpec(Step) -> Action<State, ActionInput, Output>,

    /// Return the input to the host action.
    pub action_input: FnSpec(Step, Input) -> ActionInput,
}

impl<State, Input, ActionInput, Output, Step> StateMachine<State, Input, ActionInput, Output, Step> {

    /// `next_result` is the interface that the host state machine exposes to the compound state machine.
    /// It returns whether there exists an action that is enabled by input and s.
    /// If exists, it also returns the new state and output generated by the action.
    pub open spec fn next_result(self, input: Input, s: State) -> ActionResult<State, Output> {
        if exists |step| (#[trigger] (self.step_to_action)(step).precondition)((self.action_input)(step, input), s) {
            let witness_step = choose |step| (#[trigger] (self.step_to_action)(step).precondition)((self.action_input)(step, input), s);
            let action = (self.step_to_action)(witness_step);
            let action_input = (self.action_input)(witness_step, input);
            ActionResult::Enabled((action.transition)(action_input, s).0, (action.transition)(action_input, s).1)
        } else {
            ActionResult::Disabled
        }
    }
}

/// `NetworkStateMachine` is similar to `HostStateMachine` except that it has only one action `deliver`
/// and there is no need for `step_to_action` or `action_input`.
pub struct NetworkStateMachine <#[verifier(maybe_negative)] State, #[verifier(maybe_negative)] Message> {
    /// Check if it is the initial internal state.
    pub init: FnSpec(State) -> bool,

    /// The deliver action that (1) sends zero or one message to a host and (2) takes any number of messages from a host.
    pub deliver: NetworkAction<State, Message>,
}

impl<State, Message> NetworkStateMachine<State, Message> {

    /// `next_result` is the interface that the network state machine exposes to the compound state machine.
    /// It returns whether deliver is enabled or not, and the new internal state if deliver is enabled.
    pub open spec fn next_result(self, recv: Option<Message>, s: State, send: Set<Message>) -> NetworkActionResult<State> {
        if (self.deliver.precondition)(recv, s) {
            NetworkActionResult::Enabled((self.deliver.transition)(recv, s, send))
        } else {
            NetworkActionResult::Disabled
        }
    }
}

}
