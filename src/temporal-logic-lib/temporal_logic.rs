// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus! {

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

pub type StatePred<T> = FnSpec(T) -> bool;

pub type ActionPred<T> = FnSpec(T, T) -> bool;

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

    /// `|=` for temporal predicates in TLA+.
    pub open spec fn entails(self, other: Self) -> bool {
        valid(self.implies(other))
    }
}

pub open spec fn state_pred_call<T>(state_pred: StatePred<T>, s: T) -> bool {
    state_pred(s)
}

pub open spec fn action_pred_call<T>(action_pred: ActionPred<T>, s: T, s_prime: T) -> bool {
    action_pred(s, s_prime)
}

pub open spec fn lift_state<T>(state_pred: StatePred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| state_pred_call(state_pred, ex.head()))
}

pub open spec fn lift_action<T>(action_pred: ActionPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| action_pred_call(action_pred, ex.head(), ex.head_next()))
}

pub type UnquantifiedTempPred<T, A> = FnSpec(A) -> TempPred<T>;

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
    TempPred::new(|ex: Execution<T>| exists |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

/// `~` for temporal predicates in TLA+ (i.e., `!` in Verus).
pub open spec fn not<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| !temp_pred.satisfied_by(ex))
}

/// `\A` for temporal predicates in TLA+ (i.e., `forall` in Verus).
pub open spec fn tla_forall<T, A>(unquantified_temp_pred: UnquantifiedTempPred<T, A>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |a: A| #[trigger] unquantified_temp_pred(a).satisfied_by(ex))
}

/// This lemmas is unfortunately necessary when using tla_forall.
pub proof fn use_tla_forall<T, A>(spec: TempPred<T>, unquantified_temp_pred: UnquantifiedTempPred<T, A>, a: A)
    requires
        spec.entails(tla_forall(unquantified_temp_pred)),
    ensures
        spec.entails(unquantified_temp_pred(a)),
{
    implies_unfold_auto::<T>();
    assert forall |ex: Execution<T>| #[trigger] spec.implies(unquantified_temp_pred(a)).satisfied_by(ex) by {
        assert(spec.implies(tla_forall(unquantified_temp_pred)).satisfied_by(ex));
    };
}

/// Returns a state predicate that is satisfied
/// iff `action_pred` can be satisfied by any possible following state and the current state
///
/// enabled() is used for checking whether a particular action is enabled at this **state**
///
/// Note: it says whether the action *can possibly* happen, rather than whether the action *actually does* happen!
pub open spec fn enabled<T>(action_pred: ActionPred<T>) -> StatePred<T> {
    |s: T| exists |s_prime: T| #[trigger] action_pred_call(action_pred, s, s_prime)
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
    always(tla_enabled(action_pred))
        .leads_to(lift_action(action_pred))
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
        forall |s: T| state_pred_call(init, s) ==> state_pred_call(inv, s),
        forall |s, s_prime: T| state_pred_call(inv, s) && #[trigger] action_pred_call(next, s, s_prime) ==> state_pred_call(inv, s_prime),
        spec.entails(lift_state(init).and(always(lift_action(next)))),
    ensures
        spec.entails(always(lift_state(inv))),
{}

/// See WF1 in Fig 5.
#[verifier(external_body)]
pub proof fn wf1<T>(spec: TempPred<T>, next: ActionPred<T>, forward: ActionPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        forall |s, s_prime: T| state_pred_call(p, s) && #[trigger] action_pred_call(next, s, s_prime) ==> state_pred_call(p, s_prime) || state_pred_call(q, s_prime),
        forall |s, s_prime: T| state_pred_call(p, s) && #[trigger] action_pred_call(next, s, s_prime) && #[trigger] action_pred_call(forward, s, s_prime) ==> state_pred_call(q, s_prime),
        forall |s: T| #[trigger] state_pred_call(p, s) ==> state_pred_call(enabled(forward), s),
        spec.entails(always(lift_action(next)).and(weak_fairness(forward))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q))),
{}

/// Handy lemma that combines two wf1 and leads_to_trans.
pub proof fn wf1_chain<T>(spec: TempPred<T>, next: ActionPred<T>, forward_p_q: ActionPred<T>, forward_q_r: ActionPred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        forall |s, s_prime: T| state_pred_call(p, s) && #[trigger] action_pred_call(next, s, s_prime) ==> state_pred_call(p, s_prime) || state_pred_call(q, s_prime),
        forall |s, s_prime: T| state_pred_call(p, s) && #[trigger] action_pred_call(next, s, s_prime) && #[trigger] action_pred_call(forward_p_q, s, s_prime) ==> state_pred_call(q, s_prime),
        forall |s: T| #[trigger] state_pred_call(p, s) ==> state_pred_call(enabled(forward_p_q), s),
        spec.entails(always(lift_action(next)).and(weak_fairness(forward_p_q))),
        forall |s, s_prime: T| state_pred_call(q, s) && #[trigger] action_pred_call(next, s, s_prime) ==> state_pred_call(q, s_prime) || state_pred_call(r, s_prime),
        forall |s, s_prime: T| state_pred_call(q, s) && #[trigger] action_pred_call(next, s, s_prime) && #[trigger] action_pred_call(forward_q_r, s, s_prime) ==> state_pred_call(r, s_prime),
        forall |s: T| #[trigger] state_pred_call(q, s) ==> state_pred_call(enabled(forward_q_r), s),
        spec.entails(always(lift_action(next)).and(weak_fairness(forward_q_r))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q))),
        spec.entails(lift_state(q).leads_to(lift_state(r))),
        spec.entails(lift_state(p).leads_to(lift_state(r))),
{
    wf1::<T>(spec, next, forward_p_q, p, q);
    wf1::<T>(spec, next, forward_q_r, q, r);
    leads_to_trans::<T>(spec, p, q, r);
}

#[verifier(external_body)]
pub proof fn always_p_implies_p<T>(p: StatePred<T>)
    ensures
        valid(always(lift_state(p)).implies(lift_state(p))),
{}

#[verifier(external_body)]
pub proof fn p_implies_eventually_p<T>(p: StatePred<T>)
    ensures
        valid(lift_state(p).implies(eventually(lift_state(p)))),
{}

/// Generalizes implies.
/// If we have `|= p1 => p2`, then we have `|= []p1 => []p2`

#[verifier(external_body)]
pub proof fn always_weaken<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        spec.entails(always(lift_state(p))),
        spec.entails(lift_state(p).implies(lift_state(q))),
    ensures
        spec.entails(always(lift_state(q))),
{}

/// Gets eventually p and q from always p and eventually q.
/// `|= ([]p /\ <>q) => <>(p /\ p)`

#[verifier(external_body)]
pub proof fn always_and_eventually<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        spec.entails(always(lift_state(p))),
        spec.entails(eventually(lift_state(q))),
    ensures
        spec.entails(eventually(lift_state(p).and(lift_state(q)))),
{}

/// Gets eventually q from eventually p and p implies q.
/// `|= (<>p /\ (p => q)) => <>q`

#[verifier(external_body)]
pub proof fn eventually_weaken<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        spec.entails(eventually(lift_state(p))),
        spec.entails(lift_state(p).implies(lift_state(q))),
    ensures
        spec.entails(eventually(lift_state(q))),
{}

#[verifier(external_body)]
pub proof fn eventually_weaken_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(eventually(p)),
        spec.entails(p.implies(q)),
    ensures
        spec.entails(eventually(q)),
{}

pub proof fn eventually_weaken_auto<T>(spec: TempPred<T>)
    ensures
        forall |p: TempPred<T>, q: TempPred<T>|
            valid(#[trigger] spec.implies(eventually(p))) && spec.entails(p.implies(q)) ==>
            valid(#[trigger] spec.implies(eventually(q))),
{
    assert forall |p: TempPred<T>, q: TempPred<T>|
    valid(#[trigger] spec.implies(eventually(p))) && spec.entails(p.implies(q))
    implies valid(#[trigger] spec.implies(eventually(q))) by {
        eventually_weaken_temp(spec, p, q);
    };
}

/// Gets eventually from leads_to.
/// `|= (p /\ (p ~> q)) => <>q`

/// Proves eventually q if we have p and p leads_to q.
/// `|= p /\ (p ~> q) -> <>q`
#[verifier(external_body)]
pub proof fn leads_to_apply<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        spec.entails(lift_state(p)),
        spec.entails(lift_state(p).leads_to(lift_state(q))),
    ensures
        spec.entails(eventually(lift_state(q))),
{}

/// Connects two leads_to with the transitivity of leads_to.
/// `|= ((p ~> q) /\ (q ~> r)) => (p ~> r)`
#[verifier(external_body)]
pub proof fn leads_to_trans<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        spec.entails(lift_state(p).leads_to(lift_state(q))),
        spec.entails(lift_state(q).leads_to(lift_state(r))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(r))),
{}

/// Gets (p1 leads_to q1) implies (p2 leads_to q2) if:
/// (1) p2 implies p1 and (2) q1 implies q2.
/// if we have |= p2 => p1 and |= q1 => q2
/// then we have |= (p1 ~> q1) => (p2 ~> q2)
/// TODO: have a generalized version: valid(implies(and(implies(p2, p1), implies(q1, q2)), implies(leads_to(p1, q1), leads_to(p2, q2))))
#[verifier(external_body)]
proof fn leads_to_weaken<T>(spec: TempPred<T>, p1: StatePred<T>, q1: StatePred<T>, p2: StatePred<T>, q2: StatePred<T>)
    requires
        valid(lift_state(p2).implies(lift_state(p1))),
        valid(lift_state(q1).implies(lift_state(q2))),
        spec.entails(lift_state(p1).leads_to(lift_state(q1))),
    ensures
        spec.entails(lift_state(p2).leads_to(lift_state(q2))),
{}

pub proof fn leads_to_weaken_left<T>(spec: TempPred<T>, p1: StatePred<T>, p2: StatePred<T>, q: StatePred<T>)
    requires
        valid(lift_state(p2).implies(lift_state(p1))),
        spec.entails(lift_state(p1).leads_to(lift_state(q))),
    ensures
        spec.entails(lift_state(p2).leads_to(lift_state(q))),
{
    leads_to_weaken::<T>(spec, p1, q, p2, q);
}

pub proof fn leads_to_weaken_right<T>(spec: TempPred<T>, p: StatePred<T>, q1: StatePred<T>, q2: StatePred<T>)
    requires
        valid(lift_state(q1).implies(lift_state(q2))),
        spec.entails(lift_state(p).leads_to(lift_state(q1))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q2))),
{
    leads_to_weaken::<T>(spec, p, q1, p, q2);
}

#[verifier(external_body)]
pub proof fn leads_to_always_weaken<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        spec.entails(lift_state(p).leads_to(always(lift_state(q)))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q))),
{}

/// Auto version of leads_to_weaken.
#[verifier(external_body)]
proof fn leads_to_weaken_temp<T>(spec: TempPred<T>, p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>)
    requires
        valid(p2.implies(p1)),
        valid(q1.implies(q2)),
        spec.entails(p1.leads_to(q1)),
    ensures
        spec.entails(p2.leads_to(q2)),
{}

pub proof fn leads_to_weaken_auto<T>(spec: TempPred<T>)
    ensures
        forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
            valid(p2.implies(p1)) && valid(q1.implies(q2)) && spec.entails(#[trigger] p1.leads_to(q1)) ==>
            spec.entails(#[trigger] p2.leads_to(q2))
{
    assert forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
    valid(p2.implies(p1)) && valid(q1.implies(q2)) && spec.entails(#[trigger] p1.leads_to(q1))
    implies spec.entails(#[trigger] p2.leads_to(q2)) by {
        leads_to_weaken_temp(spec, p1, q1, p2, q2);
    };
}

#[verifier(external_body)]
proof fn leads_to_eq<T>(spec: TempPred<T>, p1: StatePred<T>, q1: StatePred<T>, p2: StatePred<T>, q2: StatePred<T>)
    requires
        valid(lift_state(p2).equals(lift_state(p1))),
        valid(lift_state(q1).equals(lift_state(q2))),
        spec.entails(lift_state(p1).leads_to(lift_state(q1))),
    ensures
        spec.entails(lift_state(p2).leads_to(lift_state(q2))),
{}

#[verifier(external_body)]
proof fn leads_to_eq_temp<T>(spec: TempPred<T>, p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>)
    requires
        valid(p2.equals(p1)),
        valid(q1.equals(q2)),
        spec.entails(p1.leads_to(q1)),
    ensures
        spec.entails(p2.leads_to(q2)),
{}

pub proof fn leads_to_eq_auto<T>(spec: TempPred<T>)
    ensures
        forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
            valid(p2.equals(p1)) && valid(q1.equals(q2)) && spec.entails(#[trigger] p1.leads_to(q1)) ==>
            spec.entails(#[trigger] p2.leads_to(q2))
{
    assert forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
    valid(p2.equals(p1)) && valid(q1.equals(q2)) && spec.entails(#[trigger] p1.leads_to(q1))
    implies spec.entails(#[trigger] p2.leads_to(q2)) by {
        leads_to_eq_temp(spec, p1, q1, p2, q2);
    };
}

/// Combines leads_to using or.
/// `|= ((p ~> r) /\ (q ~> r)) == (p \/ q ~> r)`

#[verifier(external_body)]
pub proof fn leads_to_or_combine<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        spec.entails(lift_state(p).leads_to(lift_state(r))),
        spec.entails(lift_state(q).leads_to(lift_state(r))),
    ensures
        spec.entails(lift_state(p).or(lift_state(q)).leads_to(lift_state(r))),
{}

/// `|= (((p /\ q) ~> r) /\ ((p /\ ~q) ~> r)) -> (p ~> r)`

#[verifier(external_body)]
pub proof fn leads_to_combine<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        spec.entails(lift_state(p).and(lift_state(r)).leads_to(lift_state(q))),
        spec.entails(lift_state(p).and(not(lift_state(r))).leads_to(lift_state(q))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q))),
{}

/// Removes r from the premise if we have always r.
/// `|= ([]r /\ ((p /\ r) ~> q)) => (p ~> q)`
/// Note that the other direction also holds.
/// TODO: prove the equivalence.

#[verifier(external_body)]
pub proof fn leads_to_assume<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        spec.entails(always(lift_state(r))),
        spec.entails(lift_state(p).and(lift_state(r)).leads_to(lift_state(q))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q))),
{}

/// Removes not q from the premise.
/// `|= ((p /\ ~q) ~> q) => (p ~> q)`
/// Note that the other direction also holds.
/// TODO: prove the equivalence.

#[verifier(external_body)]
pub proof fn leads_to_assume_not<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        spec.entails(lift_state(p).and(not(lift_state(q))).leads_to(lift_state(q))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q))),
{}

#[verifier(external_body)]
pub proof fn leads_to_assume_not_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(p.and(not(q)).leads_to(q)),
    ensures
        spec.entails(p.leads_to(q)),
{}

#[verifier(external_body)]
pub proof fn leads_to_always_combine<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        spec.entails(lift_state(p).leads_to(always(lift_state(q)))),
        spec.entails(lift_state(p).leads_to(always(lift_state(r)))),
    ensures
        spec.entails(lift_state(p).leads_to(always(lift_state(q).and(lift_state(r))))),
{}

#[verifier(external_body)]
pub proof fn leads_to_stable<T>(spec: TempPred<T>, next: ActionPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        forall |s, s_prime: T| state_pred_call(q, s) && #[trigger] action_pred_call(next, s, s_prime) ==> state_pred_call(q, s_prime),
        spec.entails(always(lift_action(next))),
        spec.entails(lift_state(p).leads_to(lift_state(q))),
    ensures
        spec.entails(lift_state(p).leads_to(always(lift_state(q)))),
{}

}
