// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::seq::*;
use crate::pervasive::set::*;
use crate::simple_state_machine::*;
use crate::state::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn lift_state(state_pred: StatePred) -> TempPred {
    TempPred::new(|ex: Execution| state_pred.satisfied_by(ex[0]))
}

pub open spec fn lift_state_prime(state_pred: StatePred) -> TempPred {
    TempPred::new(|ex: Execution| state_pred.satisfied_by(ex[1]))
}

pub open spec fn lift_action(action_pred: ActionPred) -> TempPred {
    TempPred::new(|ex: Execution|
        exists |a: Action|
            #[trigger] action_pred.satisfied_by(a) && a.state === ex[0] && a.state_prime === ex[1]
    )
}

pub open spec fn suffix(ex: Execution, idx: nat) -> Execution {
    ex.subrange(idx as int, ex.len() as int)
}

pub open spec fn later(ex: Execution) -> Execution {
    suffix(ex, 1)
}

pub open spec fn always(temp_pred: TempPred) -> TempPred {
    TempPred::new(|ex:Execution| forall |i:nat| i<ex.len() && #[trigger] temp_pred.satisfied_by(suffix(ex, i)))
}

pub open spec fn not(temp_pred: TempPred) -> TempPred {
    // This solution is a bit hacky
    temp_pred.not()
    // But the following will significantly slow down SMT solver
    // TempPred::new(|ex:Execution| !temp_pred.satisfied_by(ex))
}

pub open spec fn and(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    // This solution is a bit hacky
    temp_pred_a.and(temp_pred_b)
    // But the following will significantly slow down SMT solver
    // TempPred::new(|ex:Execution| temp_pred_a.satisfied_by(ex) && temp_pred_b.satisfied_by(ex))
}

pub open spec fn or(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    // This solution is a bit hacky
    temp_pred_a.or(temp_pred_b)
    // But the following will significantly slow down SMT solver
    // TempPred::new(|ex:Execution| temp_pred_a.satisfied_by(ex) || temp_pred_b.satisfied_by(ex))
}

pub open spec fn eventually(temp_pred: TempPred) -> TempPred {
    not(always(not(temp_pred)))
}

pub open spec fn implies(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    or(not(temp_pred_a), temp_pred_b)
}

pub open spec fn leads_to(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    always(implies(temp_pred_a, eventually(temp_pred_b)))
}

pub open spec fn enabled(action_pred: ActionPred) -> TempPred {
    lift_state(StatePred::new(|s: SimpleState| exists |a: Action| #[trigger] action_pred.satisfied_by(a) && a.state === s))
}

pub open spec fn weak_fairness(action_pred: ActionPred) -> TempPred {
    leads_to(always(enabled(action_pred)), lift_action(action_pred))
}

pub open spec fn valid(temp_pred: TempPred) -> bool {
    forall |ex:Execution| temp_pred.satisfied_by(ex)
}

#[verifier(external_body)]
pub proof fn init_invariant(init: StatePred, next: ActionPred, inv: StatePred)
    requires
        forall |s: SimpleState| init.satisfied_by(s) ==> inv.satisfied_by(s),
        forall |a: Action| #[trigger] inv.satisfied_by(a.state) && next.satisfied_by(a) ==> inv.satisfied_by(a.state_prime),
    ensures
        valid(implies(
            and(lift_state(init), always(lift_action(next))),
            always(lift_state(inv))
        ))
{}

#[verifier(external_body)]
pub proof fn wf1(next: ActionPred, forward: ActionPred, p: StatePred, q: StatePred)
    requires
        valid(implies(
            and(lift_state(p), lift_action(next)),
            or(lift_state_prime(p), lift_state_prime(q))
        )),
        valid(implies(
            and(
                lift_state(p),
                and(lift_action(next), lift_action(forward))
            ),
            lift_state_prime(q)
        )),
        valid(implies(lift_state(p), enabled(forward))),
    ensures
        valid(implies(
            and(always(lift_action(next)), weak_fairness(forward)),
            leads_to(lift_state(p), lift_state(q))
        )),
{}

#[verifier(external_body)]
pub proof fn leads_to_apply(p: StatePred, q: StatePred)
    ensures
        valid(implies(
            and(
                lift_state(p),
                leads_to(lift_state(p), lift_state(q))
            ),
            eventually(lift_state(q))
        )),
{}

#[verifier(external_body)]
pub proof fn leads_to_trans(p: StatePred, q: StatePred, r: StatePred)
    ensures
        valid(implies(
            and(
                leads_to(lift_state(p), lift_state(q)),
                leads_to(lift_state(q),lift_state(r))
            ),
            leads_to(lift_state(p), lift_state(r))
        )),
{}

/*
Here is the reason why we need to use Set, instead of closure, for state predicate and action predicate
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
