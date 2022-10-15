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

    /// lift does not belong to the original temporal logic.
    /// Temporal logic always talks about execution/behavior from the very beginning
    /// so there is no need to lift anything.
    /// Since Verus does not have native support for temporal logic,
    /// lift allows us to implement temporal predicates on top of state/action predicates.
    pub open spec fn lift(self) -> TempPred<T> {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex.head()))
    }

    pub open spec fn lift_prime(self) -> TempPred<T> {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex.head_next()))
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

    pub open spec fn lift(self) -> TempPred<T> {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(Action{state: ex.head(), state_prime: ex.head_next()}))
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

    pub open spec fn satisfied_by(self, execution: Execution<T>) -> bool {
        (self.pred)(execution)
    }

    /// We specify all infix operators for temporal logic as TempPred methods to aid readability

    /// `/\` for temporal predicates in TLA+ (i.e., `&&` in Verus).
    pub open spec fn and(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) && other.satisfied_by(ex))
    }

    /// `\/` for temporal predicates in TLA+ (i.e., `||` in Verus).
    pub open spec fn or(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) || other.satisfied_by(ex))
    }

    /// `=>` for temporal predicates in TLA+ (i.e., `==>` in Verus).
    pub open spec fn implies(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) ==> other.satisfied_by(ex))
    }

    /// `<=>` for temporal predicates in TLA+ (i.e., `<==>` in Verus).
    pub open spec fn equals(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) <==> other.satisfied_by(ex))
    }

    /// `~>` for temporal predicates in TLA+.
    /// Returns a temporal predicate that is satisfied
    /// iff it is always the case that `self` getting satisfied implies `other` eventually getting satisfied.
    ///
    /// Defined in 3.2.3.
    pub open spec fn leads_to(self, other: Self) -> Self {
        always(self.implies(eventually(other)))
    }
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
    always(tla_enabled(action_pred))
        .leads_to(action_pred.lift())
}

/// `|=` for temporal predicates in TLA+.
/// Returns true iff `temp_pred` is satisfied by all possible executions (behaviors).
///
/// Defined in 3.3.
pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}

pub proof fn implies_unfold_auto<T>()
    ensures forall |ex: Execution<T>, p: TempPred<T>, q: TempPred<T>|
        #[trigger] valid(p.implies(q)) && p.satisfied_by(ex) ==> #[trigger] q.satisfied_by(ex),
{
    assert forall |ex: Execution<T>, p: TempPred<T>, q: TempPred<T>|
        #[trigger] valid(p.implies(q)) && p.satisfied_by(ex) implies #[trigger] q.satisfied_by(ex) by {
        assert(p.implies(q).satisfied_by(ex));
    };
}

#[verifier(external_body)]
pub proof fn init_invariant<T>(spec: TempPred<T>, init: StatePred<T>, next: ActionPred<T>, inv: StatePred<T>)
    requires
        forall |s: T| init.satisfied_by(s) ==> inv.satisfied_by(s),
        forall |a: Action<T>| inv.satisfied_by(a.state) && #[trigger] next.satisfied_by(a) ==> inv.satisfied_by(a.state_prime),
        valid(spec.implies(init.lift().and(always(next.lift())))),
    ensures
        valid(spec.implies(always(inv.lift())))
{}

/// See WF1 in Fig 5.
#[verifier(external_body)]
pub proof fn wf1<T>(spec: TempPred<T>, next: ActionPred<T>, forward: ActionPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        valid(p.lift().and(next.lift()).implies(p.lift_prime().or(q.lift_prime()))),
        valid(p.lift().and(next.lift()).and(forward.lift()).implies(q.lift_prime())),
        valid(p.lift().implies(tla_enabled(forward))),
        valid(spec.implies(always(next.lift()).and(weak_fairness(forward)))),
    ensures
        valid(spec.implies(p.lift().leads_to(q.lift()))),
{}

#[verifier(external_body)]
pub proof fn always_p_implies_p<T>(p: TempPred<T>)
    ensures
        valid(always(p).implies(p)),
{}

#[verifier(external_body)]
pub proof fn p_implies_eventually_p<T>(p: TempPred<T>)
    ensures
        valid(p.implies(eventually(p))),
{}

/// Generalizes implies.
/// If we have `|= p1 => p2`, then we have `|= []p1 => []p2`

#[verifier(external_body)]
pub proof fn always_weaken<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        valid(spec.implies(always(p))),
        valid(spec.implies(p.implies(q))),
    ensures
        valid(spec.implies(always(q))),
{}

/// Gets eventually p and q from always p and eventually q.
/// `|= ([]p /\ <>q) => <>(p /\ p)`

#[verifier(external_body)]
pub proof fn always_and_eventually<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        valid(spec.implies(always(p))),
        valid(spec.implies(eventually(q))),
    ensures
        valid(spec.implies(eventually(p.and(q)))),
{}

/// Gets eventually q from eventually p and p implies q.
/// `|= (<>p /\ (p => q)) => <>q`

#[verifier(external_body)]
pub proof fn eventually_weaken<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        valid(spec.implies(eventually(p))),
        valid(spec.implies(p.implies(q))),
    ensures
        valid(spec.implies(eventually(q))),
{}

/// Gets eventually from leads_to.
/// `|= (p /\ (p ~> q)) => <>q`

/// Proves eventually q if we have p and p leads_to q.
/// `|= p /\ (p ~> q) -> <>q`
#[verifier(external_body)]
pub proof fn leads_to_apply<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        valid(spec.implies(p)),
        valid(spec.implies(p.leads_to(q))),
    ensures
        valid(spec.implies(eventually(q))),
{}

/// Connects two leads_to with the transitivity of leads_to.
/// `|= ((p ~> q) /\ (q ~> r)) => (p ~> r)`
#[verifier(external_body)]
pub proof fn leads_to_trans<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        valid(spec.implies(p.leads_to(q))),
        valid(spec.implies(q.leads_to(r))),
    ensures
        valid(spec.implies(p.leads_to(r))),
{}

/// Gets (p1 leads_to q1) implies (p2 leads_to q2) if:
/// (1) p2 implies p1 and (2) q1 implies q2.
/// if we have |= p2 => p1 and |= q1 => q2
/// then we have |= (p1 ~> q1) => (p2 ~> q2)
/// TODO: have a generalized version: valid(implies(and(implies(p2, p1), implies(q1, q2)), implies(leads_to(p1, q1), leads_to(p2, q2))))
#[verifier(external_body)]
proof fn leads_to_weaken<T>(spec: TempPred<T>, p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>)
    requires
        valid(p2.implies(p1)),
        valid(q1.implies(q2)),
        valid(spec.implies(p1.leads_to(q1))),
    ensures
        valid(spec.implies(p2.leads_to(q2))),
{}

pub proof fn leads_to_weaken_left<T>(spec: TempPred<T>, p1: TempPred<T>, p2: TempPred<T>, q: TempPred<T>)
    requires
        valid(p2.implies(p1)),
        valid(spec.implies(p1.leads_to(q))),
    ensures
        valid(spec.implies(p2.leads_to(q))),
{
    leads_to_weaken::<T>(spec, p1, q, p2, q);
}

pub proof fn leads_to_weaken_right<T>(spec: TempPred<T>, p: TempPred<T>, q1: TempPred<T>, q2: TempPred<T>)
    requires
        valid(q1.implies(q2)),
        valid(spec.implies(p.leads_to(q1))),
    ensures
        valid(spec.implies(p.leads_to(q2))),
{
    leads_to_weaken::<T>(spec, p, q1, p, q2);
}

#[verifier(external_body)]
pub proof fn leads_to_always_weaken<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        valid(spec.implies(p.leads_to(always(q)))),
    ensures
        valid(spec.implies(p.leads_to(q))),
{}

/// Auto version of leads_to_weaken.
pub proof fn leads_to_weaken_auto<T>(spec: TempPred<T>)
    ensures
        forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
            valid(p2.implies(p1)) && valid(q1.implies(q2)) && valid(spec.implies(#[trigger] p1.leads_to(q1))) ==>
            valid(spec.implies(#[trigger] p2.leads_to(q2)))
{
    assert forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
    valid(p2.implies(p1)) && valid(q1.implies(q2)) && valid(spec.implies(#[trigger] p1.leads_to(q1)))
    implies valid(spec.implies(#[trigger] p2.leads_to(q2))) by {
        leads_to_weaken(spec, p1, q1, p2, q2);
    };
}

#[verifier(external_body)]
proof fn leads_to_eq<T>(spec: TempPred<T>, p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>)
    requires
        valid(p2.equals(p1)),
        valid(q1.equals(q2)),
        valid(spec.implies(p1.leads_to(q1))),
    ensures
        valid(spec.implies(p2.leads_to(q2))),
{}

pub proof fn leads_to_eq_auto<T>(spec: TempPred<T>)
    ensures
        forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
            valid(p2.equals(p1)) && valid(q1.equals(q2)) && valid(spec.implies(#[trigger] p1.leads_to(q1))) ==>
            valid(spec.implies(#[trigger] p2.leads_to(q2)))
{
    assert forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
    valid(p2.equals(p1)) && valid(q1.equals(q2)) && valid(spec.implies(#[trigger] p1.leads_to(q1)))
    implies valid(spec.implies(#[trigger] p2.leads_to(q2))) by {
        leads_to_eq(spec, p1, q1, p2, q2);
    };
}

/// Combines/splits leads_to using or.
/// `|= ((p ~> r) /\ (q ~> r)) == (p \/ q ~> r)`

#[verifier(external_body)]
pub proof fn leads_to_or_split<T>(p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    ensures
        valid(p.leads_to(r).and(q.leads_to(r))
               .implies(p.or(q).leads_to(r))),
        valid(p.or(q).leads_to(r)
              .implies(p.leads_to(r).and(q.leads_to(r)))),
{}

/// `|= (((p /\ q) ~> r) /\ ((p /\ ~q) ~> r)) -> (p ~> r)`

#[verifier(external_body)]
pub proof fn leads_to_split<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        valid(spec.implies(p.and(r).leads_to(q))),
        valid(spec.implies(p.and(not(r)).leads_to(q))),
    ensures
        valid(spec.implies(p.leads_to(q)))
{}

/// Removes r from the premise if we have always r.
/// `|= ([]r /\ ((p /\ r) ~> q)) => (p ~> q)`
/// Note that the other direction also holds.
/// TODO: prove the equivalence.

#[verifier(external_body)]
pub proof fn leads_to_assume<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        valid(spec.implies(always(r))),
        valid(spec.implies(p.and(r).leads_to(q))),
    ensures
        valid(spec.implies(p.leads_to(q))),
{}

/// Removes not q from the premise.
/// `|= ((p /\ ~q) ~> q) => (p ~> q)`
/// Note that the other direction also holds.
/// TODO: prove the equivalence.

#[verifier(external_body)]
pub proof fn leads_to_assume_not<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        valid(spec.implies(p.and(not(q)).leads_to(q))),
    ensures
        valid(spec.implies(p.leads_to(q))),
{}

#[verifier(external_body)]
pub proof fn leads_to_always_combine<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        valid(spec.implies(p.leads_to(always(q)))),
        valid(spec.implies(p.leads_to(always(r)))),
    ensures
        valid(spec.implies(p.leads_to(always(q.and(r))))),
{}

/// Xudong: I feel bad when mixing TempPred, ActionPred and StatePred together
#[verifier(external_body)]
pub proof fn leads_to_stable<T>(spec: TempPred<T>, next: ActionPred<T>, p: TempPred<T>, Q: StatePred<T>)
    requires
        forall |a: Action<T>| Q.satisfied_by(a.state) && #[trigger] next.satisfied_by(a) ==> Q.satisfied_by(a.state_prime),
        valid(spec.implies(always(next.lift()))),
        valid(spec.implies(p.leads_to(Q.lift()))),
    ensures
        valid(spec.implies(p.leads_to(always(Q.lift())))),
{}

}
