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

pub type Action = StatePair;
pub type Execution = Seq<SimpleState>;

pub type StatePred = Set<SimpleState>;
pub type ActionPred = Set<Action>;
pub type TempPred = Set<Execution>;

pub open spec fn lift_state(state_pred: StatePred) -> TempPred {
    Set::new(|ex: Execution| state_pred.contains(ex[0]))
}

pub open spec fn lift_action(action_pred: ActionPred) -> TempPred {
    Set::new(|ex: Execution|
        exists |a: Action|
            #[trigger] action_pred.contains(a) && a.state_0 === ex[0] && a.state_1 === ex[1]
    )
}

pub open spec fn drop(ex: Execution, idx: nat) -> Execution {
    ex.subrange(idx as int, ex.len() as int)
}

pub open spec fn later(ex: Execution) -> Execution {
    drop(ex, 1)
}

pub open spec fn always(temp_pred: TempPred) -> TempPred {
    Set::new(|ex:Execution| forall |i:nat| i<ex.len() && #[trigger] temp_pred.contains(drop(ex, i)))
}

pub open spec fn not(temp_pred: TempPred) -> TempPred {
    temp_pred.complement()
}

pub open spec fn and(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    temp_pred_a.intersect(temp_pred_b)
}

pub open spec fn or(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    temp_pred_a.union(temp_pred_b)
}

pub open spec fn eventually(temp_pred: TempPred) -> TempPred {
    not(always(not(temp_pred)))
    // Set::new(|ex:Execution| exists |i:nat| i<ex.len() && #[trigger] temp_pred.contains(drop(ex, i)))
}

pub open spec fn implies(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    or(not(temp_pred_a), temp_pred_b)
}

pub open spec fn leads_to(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    always(implies(temp_pred_a, eventually(temp_pred_b)))
}

pub open spec fn enabled(action_pred: ActionPred) -> TempPred {
    lift_state(
        Set::new(|s: SimpleState|
            exists |a: Action|
                #[trigger] action_pred.contains(a)
                && a.state_0 === s
            )
    )
}

pub open spec fn weak_fairness(action_pred: ActionPred) -> TempPred {
    leads_to(always(enabled(action_pred)), lift_action(action_pred))
}

pub open spec fn valid(temp_pred: TempPred) -> bool {
    forall |ex:Execution| temp_pred.contains(ex)
}


// pub open spec fn enabled2(action: impl Fn(SimpleState, SimpleState) -> bool, state: SimpleState) -> bool {
//     exists |s_prime: SimpleState| action(s, s_prime)
//         && #[trigger] next(s, s_prime)
// }

// pub open spec fn weak_fairness2(action: impl Fn(SimpleState, SimpleState) -> bool) -> TempPred {
//     leads_to(always(lift_state(|s: SimpleState| enabled2(action, s))),
//         lift_action(action))
// }

/*
Here is the reason why we need to use Set, instead of closure for state predicate and action predicate
If we want to write this tautology for proving safety properties:

#[verifier(external_body)]
pub proof fn init_invariant(
    init: impl Fn(SimpleState) -> bool,
    next: impl Fn(SimpleState, SimpleState) -> bool,
    inv: impl Fn(SimpleState) -> bool)
requires
    (forall |s: SimpleState| init(s) ==> inv(s))
    && (forall |s, s_prime: SimpleState| inv(s) && next(s, s_prime) ==> inv(s_prime))
ensures
    valid(implies(and(lift_state(init), always(lift_action(next))), always(lift_state(inv))))
{
}

Verus will report the following error:

error: Could not automatically infer triggers for this quantifer.  Use #[trigger] annotations to manually mark trigger terms instead.
   --> src/liveness-example/temporal_logic.rs:101:5
    |
101 |     (forall |s: SimpleState| init(s) ==> inv(s))
    |

And if we mark either init or inv as trigger, Verus will report the following error:

error: trigger must be a function call, a field access, or a bitwise operator
--> src/liveness-example/temporal_logic.rs:101:41
|
101 |     (forall |s: SimpleState| #[trigger] init(s) ==> inv(s))
|                                         ^^^^^^^

error: aborting due to 2 previous errors
*/

}
