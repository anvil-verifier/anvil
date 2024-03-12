// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::function::*;
use vstd::prelude::*;

verus! {

pub struct Execution<T> {
    pub nat_to_state: spec_fn(nat) -> T,
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

pub type StatePred<T> = spec_fn(T) -> bool;

pub type ActionPred<T> = spec_fn(T, T) -> bool;

#[verifier(reject_recursive_types(T))]
pub struct TempPred<T> {
    pub pred: spec_fn(Execution<T>) -> bool,
}

impl<T> TempPred<T> {
    pub open spec fn new(pred: spec_fn(Execution<T>) -> bool) -> Self {
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

pub open spec fn lift_state<T>(state_pred: StatePred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| state_pred(ex.head()))
}

pub open spec fn lift_state_prime<T>(state_pred: StatePred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| state_pred(ex.head_next()))
}

pub open spec fn lift_action<T>(action_pred: ActionPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| action_pred(ex.head(), ex.head_next()))
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
    TempPred::new(|ex: Execution<T>| exists |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

/// `'` (prime) for temporal predicates in TLA+.
/// Returns a temporal predicate that is satisfied iff `temp_pred` is satisfied on the suffix execution starting from the next state.
pub open spec fn later<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| temp_pred.satisfied_by(ex.suffix(1)))
}

/// `~` for temporal predicates in TLA+ (i.e., `!` in Verus).
pub open spec fn not<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| !temp_pred.satisfied_by(ex))
}

/// `\A` for temporal predicates in TLA+ (i.e., `forall` in Verus).
pub open spec fn tla_forall<T, A>(a_to_temp_pred: spec_fn(A) -> TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |a: A| #[trigger] a_to_temp_pred(a).satisfied_by(ex))
}

/// `\E` for temporal predicates in TLA+ (i.e., `exists` in Verus).
pub open spec fn tla_exists<T, A>(a_to_temp_pred: spec_fn(A) -> TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| exists |a: A| #[trigger] a_to_temp_pred(a).satisfied_by(ex))
}

pub open spec fn stable<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| temp_pred.implies(always(temp_pred)).satisfied_by(ex))
}

/// Returns a state predicate that is satisfied
/// iff `action_pred` can be satisfied by any possible following state and the current state
///
/// enabled() is used for checking whether a particular action is enabled at this **state**
///
/// Note: it says whether the action *can possibly* happen, rather than whether the action *actually does* happen!
pub open spec fn enabled<T>(action_pred: ActionPred<T>) -> StatePred<T> {
    |s: T| exists |s_prime: T| #[trigger] action_pred(s, s_prime)
}

/// Returns a temporal predicate that is satisfied
/// iff `always(lift_state(enabled(action_pred)))` getting satisfied leads to `lift_action(action_pred)` getting satisfied.
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
    always(lift_state(enabled(action_pred))).leads_to(lift_action(action_pred))
}

/// `|=` for temporal predicates in TLA+.
/// Returns true iff `temp_pred` is satisfied by all possible executions (behaviors).
///
/// Defined in 3.3.
pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}

pub open spec fn true_pred<T>() -> TempPred<T> {
    lift_state(|s: T| true)
}

}
