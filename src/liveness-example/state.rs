// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus! {

pub struct Action<T> {
    pub state: T,
    pub state_prime: T,
}

pub struct Execution<T> {
    pub nat_to_state: FnSpec(nat) -> T,
}

impl<T> Execution<T> {
    pub open spec fn head(self) -> T {
        (self.nat_to_state)(0)
    }

    pub open spec fn head_next(self) -> T {
        (self.nat_to_state)(1)
    }

    pub open spec fn suffix(self, pos: nat) -> Self {
        Execution {
            nat_to_state: |i: nat| (self.nat_to_state)(i + pos),
        }
    }
}

pub struct StatePred<#[verifier(maybe_negative)] T> {
    // It is better to keep pred private,
    // but Verus does not allow open method to access private field
    pub pred: FnSpec(T) -> bool,
}

impl<T> StatePred<T> {
    pub open spec fn new(pred: FnSpec(T) -> bool) -> Self {
        StatePred {
            pred: pred,
        }
    }

    pub open spec fn satisfied_by(self, state: T) -> bool {
        (self.pred)(state)
    }
}

pub struct ActionPred<T> {
    pub pred: FnSpec(Action<T>) -> bool,
}

impl<T> ActionPred<T> {
    pub open spec fn new(pred: FnSpec(Action<T>) -> bool) -> Self {
        ActionPred {
            pred: pred,
        }
    }

    pub open spec fn satisfied_by(self, action: Action<T>) -> bool {
        (self.pred)(action)
    }
}

pub struct TempPred<#[verifier(maybe_negative)] T> {
    pub pred: FnSpec(Execution<T>) -> bool,
}

impl<T> TempPred<T> {
    pub open spec fn new(pred: FnSpec(Execution<T>) -> bool) -> Self {
        TempPred {
            pred: pred,
        }
    }

    // This is a bit hacky as we do not want to expose pred to outside
    pub open spec fn not(temp_pred: Self) -> Self {
        TempPred {
            pred: |ex: Execution<T>| !(temp_pred.pred)(ex),
        }
    }

    pub open spec fn and(temp_pred_a: Self, temp_pred_b: Self) -> Self {
        TempPred {
            pred: |ex: Execution<T>| (temp_pred_a.pred)(ex) && (temp_pred_b.pred)(ex),
        }
    }

    pub open spec fn or(temp_pred_a: Self, temp_pred_b: Self) -> Self {
        TempPred {
            pred: |ex: Execution<T>| (temp_pred_a.pred)(ex) || (temp_pred_b.pred)(ex),
        }
    }

    pub open spec fn satisfied_by(self, execution: Execution<T>) -> bool {
        (self.pred)(execution)
    }
}

}
