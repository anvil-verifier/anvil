// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::set::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct Action<T> {
    pub state: T,
    pub state_prime: T,
}

pub type Execution<T> = FnSpec(nat) -> T;

pub struct StatePred<#[verifier(maybe_negative)] T> {
    // It is better to keep pred private,
    // but Verus does not allow open method to access private field
    pub pred: Set<T>,
}

impl<T> StatePred<T> {
    pub open spec fn new(pred: FnSpec(T) -> bool) -> Self {
        StatePred {
            pred: Set::new(|state: T| pred(state)),
        }
    }

    pub open spec fn satisfied_by(self, state: T) -> bool {
        self.pred.contains(state)
    }
}

pub struct ActionPred<T> {
    pub pred: Set<Action<T>>,
}

impl<T> ActionPred<T> {
    pub open spec fn new(pred: FnSpec(Action<T>) -> bool) -> Self {
        ActionPred {
            pred: Set::new(|action: Action<T>| pred(action)),
        }
    }

    pub open spec fn satisfied_by(self, action: Action<T>) -> bool {
        self.pred.contains(action)
    }
}

pub struct TempPred<#[verifier(maybe_negative)] T> {
    pub pred: Set<Execution<T>>,
}

impl<T> TempPred<T> {
    pub open spec fn new(pred: FnSpec(Execution<T>) -> bool) -> Self {
        TempPred {
            pred: Set::new(|execution: Execution<T>| pred(execution)),
        }
    }

    pub open spec fn satisfied_by(self, execution: Execution<T>) -> bool {
        self.pred.contains(execution)
    }

    // This is a bit hacky as we do not want to expose pred to outside
    pub open spec fn not(self) -> Self {
        TempPred {
            pred: self.pred.complement()
        }
    }

    pub open spec fn and(self, temp_pred: Self) -> Self {
        TempPred {
            pred: self.pred.intersect(temp_pred.pred)
        }
    }

    pub open spec fn or(self, temp_pred: Self) -> Self {
        TempPred {
            pred: self.pred.union(temp_pred.pred)
        }
    }
}

}
