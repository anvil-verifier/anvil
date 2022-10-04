// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::seq::*;
use crate::pervasive::set::*;
use crate::state::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn lift_state(state_pred: StatePred) -> TempPred {
    Set::new(|ex: Execution| state_pred.contains(ex[0]))
}

pub open spec fn lift_state_prime(state_pred: StatePred) -> TempPred {
    Set::new(|ex: Execution| state_pred.contains(ex[1]))
}

pub open spec fn lift_action(action_pred: ActionPred) -> TempPred {
    Set::new(|ex: Execution|
        exists |a: Action|
            #[trigger] action_pred.contains(a) && a.state === ex[0] && a.state_prime === ex[1]
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
//    or(not(temp_pred_a), temp_pred_b)
//    TODO: switched this to a first-order declaration in hope of better automation.
    Set::new(|ex: Execution| temp_pred_a.contains(ex) ==> temp_pred_b.contains(ex))
}

pub open spec fn leads_to(state_pred_a: StatePred, state_pred_b: StatePred) -> TempPred {
    always(implies(lift_state(state_pred_a), eventually(lift_state(state_pred_b))))
}

pub open spec fn tla_leads_to(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    always(implies(temp_pred_a, eventually(temp_pred_b)))
}

pub open spec fn enabled(action_pred: ActionPred) -> StatePred {
    Set::new(|s: SimpleState| exists |a: Action| #[trigger] action_pred.contains(a) && a.state === s)
}

pub open spec fn tla_enabled(action_pred: ActionPred) -> TempPred {
    lift_state(enabled(action_pred))
}

pub open spec fn weak_fairness(action_pred: ActionPred) -> TempPred {
    tla_leads_to(always(tla_enabled(action_pred)), lift_action(action_pred))
}

pub open spec fn valid(temp_pred: TempPred) -> bool {
    forall |ex:Execution| temp_pred.contains(ex)
}

pub proof fn apply_implies_once(ex: Execution, p: TempPred, q: TempPred)
    requires
        valid(implies(p, q)),
        p.contains(ex)
    ensures q.contains(ex)
{
    assert(implies(p, q).contains(ex)); // trigger valid by mentioning the contains.
}

//TODO(chris): with_triggers can't use ==> syntax? Ew.
pub proof fn apply_implies_auto()
    ensures forall |ex, p, q| with_triggers!([valid(implies(p, q)), q.contains(ex)] =>
        !(valid(implies(p, q)) && p.contains(ex)) || q.contains(ex))
{
    assert forall |ex, p, q| #[auto_trigger] valid(implies(p, q)) && p.contains(ex) implies q.contains(ex) by {
        assert(implies(p, q).contains(ex));
    }
}

#[verifier(external_body)]
pub proof fn init_invariant(init: StatePred, next: ActionPred, inv: StatePred)
    requires
        forall |s: SimpleState| init.contains(s) ==> inv.contains(s),
        forall |a: Action| #[trigger] inv.contains(a.state) && next.contains(a) ==> inv.contains(a.state_prime),
    ensures
        valid(implies(and(lift_state(init), always(lift_action(next))), always(lift_state(inv))))
{}

#[verifier(external_body)]
pub proof fn wf1(next: ActionPred, forward: ActionPred, p: StatePred, q: StatePred)
    requires
        valid(implies(and(lift_state(p), lift_action(next)), or(lift_state_prime(p), lift_state_prime(q)))),
        valid(implies(and(and(lift_state(p), lift_action(next)), lift_action(forward)), lift_state_prime(q))),
        valid(implies(lift_state(p), tla_enabled(forward))),
    ensures
        valid(implies(and(always(lift_action(next)), weak_fairness(forward)), leads_to(p, q)))
{}

// prove p ~~> q
// next is the next transition of the state machine
// forward is the key action that gets the leadsto to happen
pub proof fn make_leadsto_from_wf(forward: ActionPred, next: ActionPred, p: StatePred, q: StatePred)
    requires
        forall |act: Action| p.contains(act.state) && #[trigger] next.contains(act) ==> p.contains(act.state_prime) || q.contains(act.state_prime),
        forall |act: Action| p.contains(act.state) && #[trigger] forward.contains(act) ==> q.contains(act.state_prime),
        forall |st| #[trigger] p.contains(st) ==> enabled(forward).contains(st)
    ensures
        valid(implies(and(always(lift_action(next)), weak_fairness(forward)), leads_to(p, q)))
{
    wf1(next, forward, p, q);
}

#[verifier(external_body)]
pub proof fn leads_to_apply(p: StatePred, q: StatePred)
    ensures
        valid(implies(and(lift_state(p), leads_to(p, q)), eventually(lift_state(q))))
{}

#[verifier(external_body)]
pub proof fn leads_to_trans(p: StatePred, q: StatePred, r: StatePred)
    ensures
        valid(implies(and(leads_to(p, q), leads_to(q, r)), leads_to(p, r)))
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
