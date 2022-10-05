// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::seq::*;
use crate::pervasive::set::*;
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

pub struct Action<State> {
    pub s1: State,
    pub s2: State,
}

pub struct Execution<State> {
    pub states: Seq<State>
}

impl<State> Execution<State> {

    /// Takes an execution `ex` and returns its suffix starting from `idx`.

    pub open spec fn suffix(self, idx: nat) -> Self {
        Execution { states: self.states.subrange(idx as int, self.len() as int) }
    }

    /// Returns the suffix by removing the first state in `ex`.

    pub open spec fn later(self) -> Self {
        self.suffix(1)
    }

    pub open spec fn len(self) -> nat
    {
        self.states.len()
    }

    pub open spec fn spec_index(self, idx: int) -> State
        recommends 0 <= idx < self.len()
    {
        self.states[idx]
    }
}

pub struct StatePred<#[verifier(maybe_negative)] State> {
    // It is better to keep pred private,
    // but Verus does not allow open method to access private field
    pub pred: Set<State>,
}

impl<State> StatePred<State> {
    pub open spec fn new<F: Fn(State) -> bool>(pred: F) -> Self {
        StatePred {
            pred: Set::new(|state: State| pred(state)),
        }
    }

    pub open spec fn satisfied_by(self, state: State) -> bool {
        self.pred.contains(state)
    }

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

    pub open spec fn lift(self) -> TempPred<State> {
        TempPred::new(|ex: Execution<State>| self.satisfied_by(ex[0]))
    }

    /// Similar to lift_state except that it applies the state predicate to the second state.
    ///
    /// See P', Q' in Fig 5.
    pub open spec fn lift_primed(self) -> TempPred<State> {
        TempPred::new(|ex: Execution<State>| self.satisfied_by(ex[1]))
    }

    pub open spec fn leads_to(self, state_pred_b: Self) -> TempPred<State> {
        self.lift().leads_to(state_pred_b.lift())
    }
}

pub struct ActionPred<State> {
    pub pred: Set<Action<State>>,
}

impl<State> ActionPred<State> {
    pub open spec fn new<F: Fn(Action<State>) -> bool>(pred: F) -> Self {
        ActionPred {
            pred: Set::new(|action: Action<State>| pred(action)),
        }
    }

    pub open spec fn satisfied_by(self, action: Action<State>) -> bool {
        self.pred.contains(action)
    }

    /// Transforms an action predicate to a temporal predicate
    /// by applying the action predicate to the first two states of the execution.
    ///
    /// See A, B, N, M in Fig 5.
    pub open spec fn lift(self) -> TempPred<State> {
        TempPred::new(|ex: Execution<State>|
            exists |a: Action<State>|
                #[trigger] self.satisfied_by(a) && a.s1 === ex[0] && a.s2 === ex[1]
        )
    }
}

pub struct TempPred<State> {
    pub pred: Set<Execution<State>>,
}

impl<State> TempPred<State> {
    pub open spec fn new<F: Fn(Execution<State>) -> bool>(pred: F) -> Self {
        // TODO(verus): Want to use Self here, not TempPred, but Verus doesn't support non_struct_ctor
        TempPred {
            pred: Set::new(|execution: Execution<State>| pred(execution)),
        }
    }

    pub open spec fn satisfied_by(self, execution: Execution<State>) -> bool {
        self.pred.contains(execution)
    }

    /// `/\` (or `&&`) for temporal predicates.
    ///
    /// There is an alternative implementation below but it will significantly slow down SMT solver:
    /// ```rust
    /// TempPred::new(|ex:Execution| temp_pred_a.satisfied_by(ex) && temp_pred_b.satisfied_by(ex))
    /// ```
    pub open spec fn and(self, temp_pred: Self) -> Self {
        TempPred {
            pred: self.pred.intersect(temp_pred.pred)
        }
    }

    /// `\/` (or `||`) for temporal predicates.
    ///
    /// There is an alternative implementation below but it will significantly slow down SMT solver:
    /// ```rust
    /// TempPred::new(|ex:Execution| temp_pred_a.satisfied_by(ex) && temp_pred_b.satisfied_by(ex))
    /// ```
    pub open spec fn or(self, temp_pred: Self) -> Self {
        TempPred {
            pred: self.pred.union(temp_pred.pred)
        }
    }


    /// `==>` for temporal predicates.
    pub open spec fn implies(self, temp_pred_b: Self) -> Self {
        TempPred {
            pred: Set::new(|ex: Execution<State>| self.satisfied_by(ex) ==> temp_pred_b.satisfied_by(ex))
        }
    }

    /// Returns a temporal predicate that is satisfied
    /// iff it is always the case that `temp_pred_a` getting satisfied implies `temp_pred_b` eventually getting satisfied.
    ///
    /// Defined in 3.2.3.
    /// See ~~> (squiggly arrow) in Fig 5.

    pub open spec fn leads_to(self, temp_pred_b: Self) -> Self {
        always(self.implies(eventually(temp_pred_b)))
    }

}

/// `!` for temporal predicates.
///
/// There is an alternative implementation below but it will significantly slow down SMT solver:
/// ```rust
/// TempPred::new(|ex:Execution| temp_pred_a.satisfied_by(ex) && temp_pred_b.satisfied_by(ex))
/// ```
pub open spec fn not<State>(temp_pred: TempPred<State>) -> TempPred<State> {
    TempPred {
        pred: temp_pred.pred.complement()
    }
}

/// Returns a temporal predicate that is satisfied iff `temp_pred` is satisfied on every suffix of the execution.
///
/// Defined in 3.1.
/// See [] (box) in Fig 5.

pub open spec fn always<State>(temp_pred: TempPred<State>) -> TempPred<State> {
    TempPred::new(|ex: Execution<State>| forall |i:nat| i<ex.len() ==> #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

/// Returns a temporal predicate that is satisfied iff `temp_pred` is satisfied on at least one suffix of the execution.
///
/// Defined in 3.2.1.
/// See <> (diamond) in Fig 5.

pub open spec fn eventually<State>(temp_pred: TempPred<State>) -> TempPred<State> {
    TempPred::new(|ex: Execution<State>| exists |i:nat| i<ex.len() && #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}


/// Returns a temporal predicate that is satisfied
/// iff `action_pred` can be satisfied by any possible execution starting with the current state.
///
/// Defined in 2.7.
/// See Enabled in Fig 5.
///
/// Note: it says whether the action *can possibly* happen, rather than whether the action *actually does* happen!

pub open spec fn enabled<State>(action_pred: ActionPred<State>) -> TempPred<State> {
    StatePred::new(|s1: State| exists |s2: State| #[trigger] action_pred.satisfied_by(Action{s1, s2})).lift()
}

/// Returns a temporal predicate that is satisfied
/// iff `always(enabled(action_pred))` getting satisfied leads to `lift_action(action_pred)` getting satisfied.
///
/// It says whether it is *always* the case that if the action is *always* enabled, the action *eventually* happens.
///
/// Defined in 5.3 in a different form.
/// We can prove the two forms are the same:
///     []E(A) ~~> A
/// === []([]E(A) -> <>A)
/// === [](![]E(A) \/ <>A)
/// === [](!!<>!E(A) \/ <>A)    <--- apply always_to_eventually
/// === [](<>!E(A) \/ <>A)
/// === []<>(!E(A) \/ A)      <--- apply eventually_or
/// === []<>!E(A) \/ []<>A    <--- apply always_eventually_distrib
/// === []<>A \/ []<>!E(A)
///
/// See WF in Fig 5.

pub open spec fn weak_fairness<State>(action_pred: ActionPred<State>) -> TempPred<State> {
    leads_to(always(enabled(action_pred)), action_pred.lift())
}

// TODO move these proofs to a _v file

/// Returns true iff `temp_pred` is satisfied by all possible executions (behaviors).
/// Defined in 3.3.
/// See |= in Fig 5.

pub open spec fn valid<State>(temp_pred: TempPred<State>) -> bool {
    forall |ex:Execution| temp_pred.satisfied_by(ex)
}

#[verifier(external_body)]
pub proof fn init_invariant<State>(init: StatePred<State>, next: ActionPred<State>, inv: StatePred<State>)
    requires
        forall |s: State| init.satisfied_by(s) ==> inv.satisfied_by(s),
        forall |a: Action| #[trigger] inv.satisfied_by(a.state) && next.satisfied_by(a) ==> inv.satisfied_by(a.state_prime),
    ensures
        valid(implies(
            and(lift_state(init), always(lift_action(next))),
            always(lift_state(inv))
        ))
{}

/// See WF1 in Fig 5.

#[verifier(external_body)]
pub proof fn wf1<State>(next: ActionPred<State>, forward: ActionPred<State>, p: StatePred<State>, q: StatePred<State>)
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

/*
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
*/

}
