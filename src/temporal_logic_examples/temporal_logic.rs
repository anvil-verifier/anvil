// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pred::*;
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
    enabled(action_pred).lift()
}

/// Returns a temporal predicate that is satisfied
/// iff `always(tla_enabled(action_pred))` getting satisfied leads to `action_pred.lift()` getting satisfied.
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
    leads_to(always(tla_enabled(action_pred)), action_pred.lift())
}

/// `|=` for temporal predicates in TLA+.
/// Returns true iff `temp_pred` is satisfied by all possible executions (behaviors).
///
/// Defined in 3.3.

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}

#[verifier(external_body)]
pub proof fn init_invariant<T>(init: StatePred<T>, next: ActionPred<T>, inv: StatePred<T>)
    requires
        forall |s: T| init.satisfied_by(s) ==> inv.satisfied_by(s),
        forall |a: Action<T>| inv.satisfied_by(a.state) && #[trigger] next.satisfied_by(a) ==> inv.satisfied_by(a.state_prime),
    ensures
        valid(implies(
            and(init.lift(), always(next.lift())),
            always(inv.lift())
        ))
{}

/// See WF1 in Fig 5.

#[verifier(external_body)]
pub proof fn wf1<T>(next: ActionPred<T>, forward: ActionPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        valid(implies(
            and(p.lift(), next.lift()),
            or(p.lift_prime(), q.lift_prime())
        )),
        valid(implies(
            and(
                p.lift(),
                and(next.lift(), forward.lift())
            ),
            q.lift_prime()
        )),
        valid(implies(p.lift(), tla_enabled(forward))),
    ensures
        valid(implies(
            and(always(next.lift()), weak_fairness(forward)),
            leads_to(p.lift(), q.lift())
        )),
{}

pub proof fn apply_implies_auto<T>()
    ensures forall |ex: Execution<T>, p, q: TempPred<T>|
        #[trigger] valid(implies(p, q)) && p.satisfied_by(ex) ==> #[trigger] q.satisfied_by(ex),
{
    assert forall |ex: Execution<T>, p, q: TempPred<T>|
        #[trigger] valid(implies(p, q)) && p.satisfied_by(ex) implies #[trigger] q.satisfied_by(ex) by {
        assert(implies(p, q).satisfied_by(ex));
    };
}


/// Generalizes implies.
/// If we have `|= p1 -> p2`, then we have `|= []p1 -> []p2`

#[verifier(external_body)]
pub proof fn implies_generalize<T>(p1: TempPred<T>, p2: TempPred<T>)
    ensures
        valid(implies(p1, p2)) ==> valid(implies(always(p1), always(p2))),
{}

/// Auto version of implies_generalize.

pub proof fn implies_generalize_auto<T>()
    ensures
        forall |p1: TempPred<T>, p2: TempPred<T>| #[trigger] valid(implies(p1, p2)) ==> valid(implies(always(p1), always(p2))),
{
    assert forall |p1: TempPred<T>, p2: TempPred<T>| valid(implies(p1, p2)) implies #[trigger] valid(implies(always(p1), always(p2))) by {
        implies_generalize::<T>(p1, p2);
    }
}

/// Gets eventually p and q from always p and eventually q.
/// `|= ([]p /\ <>q) -> <>(p /\ p)`

#[verifier(external_body)]
pub proof fn always_and_eventually<T>(p: TempPred<T>, q: TempPred<T>)
    ensures
        valid(implies(
            and(always(p), eventually(q)),
            eventually(and(p, q))
        ))
{}

/// Gets eventually q from eventually p and p implies q.
/// `|= (<>p /\ (p -> q)) -> <>q`

#[verifier(external_body)]
pub proof fn eventually_weaken<T>(p: TempPred<T>, q: TempPred<T>)
    ensures
        valid(implies(
            and(eventually(p), implies(p, q)),
            eventually(q)
        )),
{}

/// Gets eventually from leads_to.
/// `|= (p /\ (p ~> q)) -> <>q`

#[verifier(external_body)]
pub proof fn leads_to_apply<T>(p: StatePred<T>, q: StatePred<T>)
    ensures
        valid(implies(
            and(
                p.lift(),
                leads_to(p.lift(), q.lift())
            ),
            eventually(q.lift())
        )),
{}

/// Connects two leads_to with the transitivity of leads_to.
/// `|= ((p ~> q) /\ (q ~> r)) -> (p ~> r)`

#[verifier(external_body)]
pub proof fn leads_to_trans<T>(p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    ensures
        valid(implies(
            and(
                leads_to(p.lift(), q.lift()),
                leads_to(q.lift(), r.lift())
            ),
            leads_to(p.lift(), r.lift())
        )),
{}

/// Gets (p1 leads_to q1) implies (p2 leads_to q2) if:
/// (1) p2 implies p1 and (2) q1 implies q2.
/// if we have |= p2 -> p1 and |= q1 -> q2
/// then we have |= (p1 ~> q1) -> (p2 ~> q2)

#[verifier(external_body)]
pub proof fn leads_to_weaken<T>(p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>)
    ensures
        valid(implies(p2, p1)) && valid(implies(q1, q2)) ==> valid(implies(leads_to(p1, q1), leads_to(p2, q2))),
{}

/// Auto version of leads_to_weaken.

pub proof fn leads_to_weaken_auto<T>()
    ensures
        forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
            valid(implies(p2, p1)) && valid(implies(q1, q2)) ==> valid(implies(#[trigger] leads_to(p1, q1), #[trigger] leads_to(p2, q2)))
{
    assert forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>| valid(implies(p2, p1)) && valid(implies(q1, q2))
    implies valid(implies(#[trigger] leads_to(p1, q1), #[trigger] leads_to(p2, q2))) by {
        leads_to_weaken(p1, q1, p2, q2);
    };
}

/// Combines/splits leads_to using or.
/// `|= ((p ~> r) /\ (q ~> r)) == (p \/ q ~> r)`

#[verifier(external_body)]
pub proof fn leads_to_or_split<T>(p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    ensures
        valid(implies(and(#[trigger] leads_to(p, r), #[trigger] leads_to(q, r)), leads_to(or(p, q), r))),
        valid(implies(leads_to(or(p, q), r), and(#[trigger] leads_to(p, r), #[trigger] leads_to(q, r)))),
{}

/// Removes r from the premise if we have always r.
/// `|= ([]r /\ ((p /\ r) ~> q)) -> (p ~> q)`
/// Note that the other direction also holds.
/// TODO: prove the equivalence.

#[verifier(external_body)]
pub proof fn leads_to_assume<T>(p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    ensures
        valid(implies(and(#[trigger] always(r), #[trigger] leads_to(and(p, r), q)), leads_to(p, q))),
        // valid(implies(and(#[trigger] always(r), #[trigger] leads_to(p, q)), leads_to(and(p, r), q))),
{}

/// Removes not q from the premise.
/// `|= ((p /\ ~q) ~> q) -> (p ~> q)`
/// Note that the other direction also holds.
/// TODO: prove the equivalence.

#[verifier(external_body)]
pub proof fn leads_to_assume_not<T>(p: TempPred<T>, q: TempPred<T>)
    ensures
        valid(implies(#[trigger] leads_to(and(p, not(q)), q), leads_to(p, q))),
        // valid(implies(#[trigger] leads_to(p, q), leads_to(and(p, not(q)), q))),
{}

}
