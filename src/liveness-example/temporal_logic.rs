// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::set::*;
use crate::state::*;
use builtin::*;
use builtin_macros::*;

verus! {

/// Implement the temporal logic described in the paper "The Temporal Logic of Actions."
///
/// Note:
/// The paper uses [A]_f as an abbreviation of A || (f' = f)
/// and <A>_f as an abbreviation of A && (f' != f)
/// where f' = f represents a stuttering step.
/// But here we assume the caller ensures whether the action allows a stuttering step when passing the arguments.
///
/// TODO: Explicitly allow or disallow stuttering step.


/// Transforms a state predicate to a temporal predicate
/// by applying the state predicate to the first state of the execution (behavior).
///
/// See P, Q, I in Fig 5.
///
/// Note:
/// lift_state, as well as lift_state_prime and lift_action, does not belong to the original temporal logic
/// because temporal logic always talks about execution/behavior from the very beginning so there is no need to lift anything.
/// Since Verus does not have native support for temporal logic,
/// lift_xxx allows us to implement temporal predicates on top of state/action predicates.

pub open spec fn lift_state<T>(state_pred: StatePred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| state_pred.satisfied_by(ex.head()))
}

/// Similar to lift_state except that it applies the state predicate to the second state.
///
/// See P', Q' in Fig 5.

pub open spec fn lift_state_prime<T>(state_pred: StatePred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| state_pred.satisfied_by(ex.head_next()))
}

/// Transforms an action predicate to a temporal predicate
/// by applying the action predicate to the first two states of the execution.
///
/// See A, B, N, M in Fig 5.

pub open spec fn lift_action<T>(action_pred: ActionPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>|
        exists |a: Action<T>| #[trigger] action_pred.satisfied_by(a) && a.state === ex.head() && a.state_prime === ex.head_next()
    )
}

/// `~` for temporal predicates in TLA+ (i.e., `!` in Verus).

pub open spec fn not<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| !temp_pred.satisfied_by(ex))
}

/// `/\` for temporal predicates in TLA+ (i.e., `&&` in Verus).

pub open spec fn and<T>(temp_pred_a: TempPred<T>, temp_pred_b: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| temp_pred_a.satisfied_by(ex) && temp_pred_b.satisfied_by(ex))
}

/// `\/` for temporal predicates in TLA+ (i.e., `||` in Verus).

pub open spec fn or<T>(temp_pred_a: TempPred<T>, temp_pred_b: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| temp_pred_a.satisfied_by(ex) || temp_pred_b.satisfied_by(ex))
}

/// `=>` for temporal predicates in TLA+ (i.e., `==>` in Verus).

pub open spec fn implies<T>(temp_pred_a: TempPred<T>, temp_pred_b: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| temp_pred_a.satisfied_by(ex) ==> temp_pred_b.satisfied_by(ex))
}

/// `[]` for temporal predicates in TLA+.
/// Returns a temporal predicate that is satisfied iff `temp_pred` is satisfied on every suffix of the execution.
///
/// Defined in 3.1.

pub open spec fn always<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

/// `<>` for temporal predicates in TLA+.
/// Returns a temporal predicate that is satisfied iff `temp_pred` is satisfied on at least one suffix of the execution.
///
/// Defined in 3.2.1.

pub open spec fn eventually<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    not(always(not(temp_pred)))
}

/// `~>` for temporal predicates in TLA+.
/// Returns a temporal predicate that is satisfied
/// iff it is always the case that `temp_pred_a` getting satisfied implies `temp_pred_b` eventually getting satisfied.
///
/// Defined in 3.2.3.

pub open spec fn leads_to<T>(temp_pred_a: TempPred<T>, temp_pred_b: TempPred<T>) -> TempPred<T> {
    always(implies(temp_pred_a, eventually(temp_pred_b)))
}

/// Returns a state predicate that is satisfied
/// iff `action_pred` can be satisfied by any possible following state and the current state
///
/// enabled() is used for checking whether a particular action is enabled at this **state**
///
/// Note: it says whether the action *can possibly* happen, rather than whether the action *actually does* happen!

pub open spec fn enabled<T>(action_pred: ActionPred<T>) -> StatePred<T> {
    StatePred::new(|s: T| exists |s_prime: T| #[trigger] action_pred.satisfied_by(Action{state: s, state_prime: s_prime}))
}

/// Returns a temporal predicate that is satisfied
/// iff `action_pred` can be satisfied by any possible execution starting with the current state.
///
/// Different from enabled(), tla_enabled() is used for checking whether the action is enabled at (the first state) of this **execution**
///
/// Defined in 2.7.
///
/// Note: it says whether the action *can possibly* happen, rather than whether the action *actually does* happen!

pub open spec fn tla_enabled<T>(action_pred: ActionPred<T>) -> TempPred<T> {
    lift_state(enabled(action_pred))
}

/// Returns a temporal predicate that is satisfied
/// iff `always(tla_enabled(action_pred))` getting satisfied leads to `lift_action(action_pred)` getting satisfied.
///
/// It says whether it is *always* the case that if the action is *always* enabled, the action *eventually* happens.
///
/// Defined in 5.3 in a different form.
/// We can prove the two forms are the same:
///    []E(A) ~> A
/// == []([]E(A) => <>A)
/// == [](~[]E(A) \/ <>A)
/// == [](~~<>~E(A) \/ <>A)  <--- apply always_to_eventually
/// == [](<>~E(A) \/ <>A)
/// == []<>(~E(A) \/ A)      <--- apply eventually_or
/// == []<>~E(A) \/ []<>A    <--- apply always_eventually_distrib
/// == []<>A \/ []<>~E(A)

pub open spec fn weak_fairness<T>(action_pred: ActionPred<T>) -> TempPred<T> {
    leads_to(always(tla_enabled(action_pred)), lift_action(action_pred))
}

/// `|=` for temporal predicates in TLA+.
/// Returns true iff `temp_pred` is satisfied by all possible executions (behaviors).
///
/// Defined in 3.3.

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}

pub proof fn apply_implies_auto<T>()
    ensures forall |ex: Execution<T>, p, q: TempPred<T>|
        #[trigger] valid(implies(p, q)) && p.satisfied_by(ex) ==> #[trigger] q.satisfied_by(ex),
{
    assert forall |ex: Execution<T>, p, q: TempPred<T>|
        #[trigger] valid(implies(p, q)) && p.satisfied_by(ex) implies #[trigger] q.satisfied_by(ex) by {
        assert(implies(p, q).satisfied_by(ex));
    };
}

#[verifier(external_body)]
pub proof fn init_invariant<T>(init: StatePred<T>, next: ActionPred<T>, inv: StatePred<T>)
    requires
        forall |s: T| init.satisfied_by(s) ==> inv.satisfied_by(s),
        forall |a: Action<T>| #[trigger] inv.satisfied_by(a.state) && next.satisfied_by(a) ==> inv.satisfied_by(a.state_prime),
    ensures
        valid(implies(
            and(lift_state(init), always(lift_action(next))),
            always(lift_state(inv))
        ))
{}

/// See WF1 in Fig 5.

#[verifier(external_body)]
pub proof fn wf1<T>(next: ActionPred<T>, forward: ActionPred<T>, p: StatePred<T>, q: StatePred<T>)
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
        valid(implies(lift_state(p), tla_enabled(forward))),
    ensures
        valid(implies(
            and(always(lift_action(next)), weak_fairness(forward)),
            leads_to(lift_state(p), lift_state(q))
        )),
{}

/// Proves eventually q if we have p and p leads_to q.
/// `|= p /\ (p ~> q) -> <>q`

#[verifier(external_body)]
pub proof fn leads_to_apply<T>(p: StatePred<T>, q: StatePred<T>)
    ensures
        valid(implies(
            and(
                lift_state(p),
                leads_to(lift_state(p), lift_state(q))
            ),
            eventually(lift_state(q))
        )),
{}

/// Proves transitivity of leads_to.
/// `|= (p ~> q) /\ (q ~> r) -> (p ~> r)`

#[verifier(external_body)]
pub proof fn leads_to_trans<T>(p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    ensures
        valid(implies(
            and(
                leads_to(lift_state(p), lift_state(q)),
                leads_to(lift_state(q),lift_state(r))
            ),
            leads_to(lift_state(p), lift_state(r))
        )),
{}

}
