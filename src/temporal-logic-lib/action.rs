// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus! {

pub struct HostAction<#[verifier(maybe_negative)] S, #[verifier(maybe_negative)] I, #[verifier(maybe_negative)] O> {
    pub precondition: FnSpec(I, S) -> bool,
    pub transition: FnSpec(I, S) -> S,
    pub output: FnSpec(I, S) -> O,
}

impl<S, I, O> HostAction<S, I, O> {
    pub open spec fn satisfied_by(self, input: I, s: S, s_prime: S) -> bool {
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
