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

pub struct Action {
    pub state: SimpleState,
    pub state_prime: SimpleState,
}

pub type Execution = Seq<SimpleState>;

pub struct StatePred {
    // It is better to keep pred private,
    // but Verus does not allow open method to access private field
    pub pred: Set<SimpleState>,
}

impl StatePred {
    pub open spec fn new<F: Fn(SimpleState) -> bool>(pred: F) -> StatePred {
        StatePred {
            pred: Set::new(|state: SimpleState| pred(state)),
        }
    }

    pub open spec fn satisfies(self, state: SimpleState) -> bool {
        self.pred.contains(state)
    }
}

pub struct ActionPred {
    pub pred: Set<Action>,
}

impl ActionPred {
    pub open spec fn new<F: Fn(Action) -> bool>(pred: F) -> ActionPred {
        ActionPred {
            pred: Set::new(|action: Action| pred(action)),
        }
    }

    pub open spec fn satisfies(self, action: Action) -> bool {
        self.pred.contains(action)
    }
}

pub struct TempPred {
    pub pred: Set<Execution>,
}

impl TempPred {
    pub open spec fn new<F: Fn(Execution) -> bool>(pred: F) -> TempPred {
        TempPred {
            pred: Set::new(|execution: Execution| pred(execution)),
        }
    }

    pub open spec fn satisfies(self, execution: Execution) -> bool {
        self.pred.contains(execution)
    }

    // This is a bit hacky as we do not want to expose pred to outside
    pub open spec fn not(self) -> TempPred {
        TempPred {
            pred: self.pred.complement()
        }
    }

    pub open spec fn and(self, temp_pred: TempPred) -> TempPred {
        TempPred {
            pred: self.pred.intersect(temp_pred.pred)
        }
    }

    pub open spec fn or(self, temp_pred: TempPred) -> TempPred {
        TempPred {
            pred: self.pred.union(temp_pred.pred)
        }
    }
}

}
