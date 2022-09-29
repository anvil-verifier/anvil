// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#[allow(unused_imports)]
use crate::pervasive::seq::*;
#[allow(unused_imports)]
use crate::pervasive::set::*;
#[allow(unused_imports)]
use crate::simple_state_machine::*;
#[allow(unused_imports)]
use crate::state::*;
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

pub struct Execution {
    pub states: Seq<SimpleState>, // Pretend it is infinite
}

type TempPred = Set<Execution>;

pub open spec fn lift_state(state_pred: impl Fn(SimpleState) -> bool) -> TempPred {
    Set::new(|ex: Execution| state_pred(ex.states[0]))
}

pub open spec fn lift_action(action_pred: impl Fn(SimpleState, SimpleState) -> bool) -> TempPred {
    Set::new(|ex: Execution| action_pred(ex.states[0], ex.states[1]))
}

pub open spec fn drop(ex: Execution, idx: nat) -> Execution {
    Execution {
        states: ex.states.subrange(idx as int, ex.states.len() as int)
    }
}

pub open spec fn temp_always(temp_pred: TempPred) -> TempPred {
    Set::new(|ex:Execution| forall |i:nat| i<ex.states.len() && #[trigger] temp_pred.contains(drop(ex, i)))
}

pub open spec fn temp_not(temp_pred: TempPred) -> TempPred {
    temp_pred.complement()
}

pub open spec fn temp_and(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    temp_pred_a.intersect(temp_pred_b)
}

pub open spec fn temp_or(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    temp_pred_a.union(temp_pred_b)
}

pub open spec fn temp_eventually(temp_pred: TempPred) -> TempPred {
    temp_not(temp_always(temp_not(temp_pred)))
    // Set::new(|ex:Execution| exists |i:nat| i<ex.states.len() && #[trigger] temp_pred.contains(drop(ex, i)))
}

pub open spec fn temp_implies(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    temp_or(temp_not(temp_pred_a), temp_pred_b)
}

pub open spec fn temp_leads_to(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    temp_always(temp_implies(temp_pred_a, temp_eventually(temp_pred_b)))
}

pub open spec fn enabled(action: impl Fn(SimpleState, SimpleState) -> bool) -> TempPred {
    lift_state(|s: SimpleState|
        exists |s_prime: SimpleState| action(s, s_prime)
            && #[trigger] next(s, s_prime)
    )
}

pub open spec fn weak_fairness(action: impl Fn(SimpleState, SimpleState) -> bool) -> TempPred {
    temp_leads_to(temp_always(enabled(action)), lift_action(action))
    // temp_always(temp_implies(temp_always(enabled(action)), temp_eventually(lift_action(action))))
}


// pub open spec fn enabled2(action: impl Fn(SimpleState, SimpleState) -> bool, state: SimpleState) -> bool {
//     exists |s_prime: SimpleState| action(s, s_prime)
//         && #[trigger] next(s, s_prime)
// }

// pub open spec fn weak_fairness2(action: impl Fn(SimpleState, SimpleState) -> bool) -> TempPred {
//     temp_leads_to(temp_always(lift_state(|s: SimpleState| enabled2(action, s))),
//         lift_action(action))
// }

}
