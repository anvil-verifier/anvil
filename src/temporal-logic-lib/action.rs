// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus! {

pub struct HostAction<#[verifier(maybe_negative)] State, #[verifier(maybe_negative)] Input, #[verifier(maybe_negative)] Output> {
    pub precondition: FnSpec(Input, State) -> bool,
    pub transition: FnSpec(Input, State) -> State,
    pub output: FnSpec(Input, State) -> Output,
}

impl<State, Input, Output> HostAction<State, Input, Output> {
    pub open spec fn satisfied_by(self, input: Input, s: State, s_prime: State) -> bool {
        &&& (self.precondition)(input, s)
        &&& s_prime === (self.transition)(input, s)
    }
}

pub struct NetworkAction<#[verifier(maybe_negative)] S, #[verifier(maybe_negative)] Recv, #[verifier(maybe_negative)] Send> {
    pub precondition: FnSpec(Recv, S) -> bool,
    pub transition: FnSpec(Recv, S, Send) -> S,
}

impl<S, Recv, Send> NetworkAction<S, Recv, Send> {
    pub open spec fn satisfied_by(self, recv: Recv, s: S, s_prime: S, send: Send) -> bool {
        &&& (self.precondition)(recv, s)
        &&& s_prime === (self.transition)(recv, s, send)
    }
}

}
