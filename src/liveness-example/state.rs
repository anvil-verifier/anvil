// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::seq::*;
use crate::pervasive::set::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub enum ABC {
    A,
    B,
    C,
}

pub struct SimpleState {
    pub x: ABC,
    pub happy: bool,
}

pub struct Action<T> {
    pub state: T,
    pub state_prime: T,
}

pub type Execution<T> = Seq<T>;

/// TODO: Make StatePred, ActionPred and TempPred generic and take any form of state/action/execution

pub struct StatePred<#[verifier(maybe_negative)] T> {
    // It is better to keep pred private,
    // but Verus does not allow open method to access private field
    pub pred: Set<T>,
}

impl<T> StatePred<T> {
    pub open spec fn new<F: Fn(T) -> bool>(pred: F) -> StatePred<T> {
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
    pub open spec fn new<F: Fn(Action<T>) -> bool>(pred: F) -> ActionPred<T> {
        ActionPred {
            pred: Set::new(|action: Action<T>| pred(action)),
        }
    }

    pub open spec fn satisfied_by(self, action: Action<T>) -> bool {
        self.pred.contains(action)
    }
}

pub struct TempPred<T> {
    pub pred: Set<Execution<T>>,
}

impl<T> TempPred<T> {
    pub open spec fn new<F: Fn(Execution<T>) -> bool>(pred: F) -> TempPred<T> {
        TempPred {
            pred: Set::new(|execution: Execution<T>| pred(execution)),
        }
    }

    pub open spec fn satisfied_by(self, execution: Execution<T>) -> bool {
        self.pred.contains(execution)
    }

    // This is a bit hacky as we do not want to expose pred to outside
    pub open spec fn not(self) -> TempPred<T> {
        TempPred {
            pred: self.pred.complement()
        }
    }

    pub open spec fn and(self, temp_pred: TempPred<T>) -> TempPred<T> {
        TempPred {
            pred: self.pred.intersect(temp_pred.pred)
        }
    }

    pub open spec fn or(self, temp_pred: TempPred<T>) -> TempPred<T> {
        TempPred {
            pred: self.pred.union(temp_pred.pred)
        }
    }
}

}
