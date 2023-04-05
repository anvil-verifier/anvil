// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::function::*;
use crate::pervasive::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;

verus! {

proof fn later_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        later(p).satisfied_by(ex),
    ensures
        p.satisfied_by(ex.suffix(1)),
{}

proof fn always_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        always(p).satisfied_by(ex),
    ensures
        forall |i: nat| p.satisfied_by(#[trigger] ex.suffix(i)),
{}

proof fn eventually_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        eventually(p).satisfied_by(ex),
    ensures
        exists |i: nat| p.satisfied_by(#[trigger] ex.suffix(i)),
{}

proof fn not_eventually_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        not(eventually(p)).satisfied_by(ex),
    ensures
        forall |i| !p.satisfied_by(#[trigger] ex.suffix(i))
{}

proof fn stable_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        stable(p).satisfied_by(ex),
    ensures
        p.satisfied_by(ex) ==> forall |i| p.satisfied_by(#[trigger] ex.suffix(i)),
{}

proof fn leads_to_unfold<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.leads_to(q).satisfied_by(ex),
    ensures
        forall |i: nat| p.implies(eventually(q)).satisfied_by(#[trigger] ex.suffix(i)),
{
    always_unfold::<T>(ex, p.implies(eventually(q)));
}

proof fn weak_fairness_unfold<T>(ex: Execution<T>, p: ActionPred<T>)
    requires
        weak_fairness(p).satisfied_by(ex),
    ensures
        forall |i| always(lift_state(enabled(p))).implies(eventually(lift_action(p))).satisfied_by(#[trigger] ex.suffix(i)),
{
    leads_to_unfold::<T>(ex, always(lift_state(enabled(p))), lift_action(p));
}

proof fn always_lift_state_unfold<T>(ex: Execution<T>, p: StatePred<T>)
    requires
        always(lift_state(p)).satisfied_by(ex),
    ensures
        forall |i| p(#[trigger] ex.suffix(i).head()),
{
    always_unfold::<T>(ex, lift_state(p));
}

proof fn always_lift_action_unfold<T>(ex: Execution<T>, p: ActionPred<T>)
    requires
        always(lift_action(p)).satisfied_by(ex),
    ensures
        forall |i| p(#[trigger] ex.suffix(i).head(), ex.suffix(i).head_next()),
{
    always_unfold::<T>(ex, lift_action(p));
}

proof fn tla_forall_unfold<T, A>(ex: Execution<T>, a_to_p: FnSpec(A) -> TempPred<T>)
    requires
        tla_forall(a_to_p).satisfied_by(ex),
    ensures
        forall |a| #[trigger] a_to_p(a).satisfied_by(ex),
{}

proof fn tla_exists_unfold<T, A>(ex: Execution<T>, a_to_p: FnSpec(A) -> TempPred<T>)
    requires
        tla_exists(a_to_p).satisfied_by(ex),
    ensures
        exists |a| #[trigger] a_to_p(a).satisfied_by(ex),
{}

proof fn tla_exists_proved_by_witness<T, A>(ex: Execution<T>, a_to_p: FnSpec(A) -> TempPred<T>, witness_a: A)
    requires
        a_to_p(witness_a).satisfied_by(ex),
    ensures
        tla_exists(a_to_p).satisfied_by(ex)
{}

spec fn tla_exists_choose_witness<T, A>(ex: Execution<T>, a_to_p: FnSpec(A) -> TempPred<T>) -> A
    recommends
        exists |a| #[trigger] a_to_p(a).satisfied_by(ex),
{
    let witness = choose |a| #[trigger] a_to_p(a).satisfied_by(ex);
    witness
}

proof fn implies_apply<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.implies(q).satisfied_by(ex),
        p.satisfied_by(ex),
    ensures
        q.satisfied_by(ex),
{}

proof fn implies_contraposition_apply<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.implies(q).satisfied_by(ex),
        not(q).satisfied_by(ex),
    ensures
        not(p).satisfied_by(ex),
{}

proof fn equals_apply<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.equals(q).satisfied_by(ex),
        p.satisfied_by(ex),
    ensures
        q.satisfied_by(ex),
{}

proof fn implies_apply_with_always<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        always(p.implies(q)).satisfied_by(ex),
        always(p).satisfied_by(ex),
    ensures
        always(q).satisfied_by(ex),
{
    always_unfold::<T>(ex, p.implies(q));
    always_unfold::<T>(ex, p);
}

proof fn entails_apply<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.entails(q),
        p.satisfied_by(ex),
    ensures
        q.satisfied_by(ex),
{
    implies_apply::<T>(ex, p, q);
}

proof fn entails_apply_auto<T>()
    ensures
        forall |ex: Execution<T>, p: TempPred<T>, q: TempPred<T>| #[trigger] p.entails(q) && p.satisfied_by(ex)
            ==> #[trigger] q.satisfied_by(ex),
{
    assert forall |ex: Execution<T>, p: TempPred<T>, q: TempPred<T>|
    #[trigger] valid(p.implies(q)) && p.satisfied_by(ex) implies #[trigger] q.satisfied_by(ex) by {
        entails_apply(ex, p, q);
    };
}

pub proof fn entails_trans<T>(p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        p.entails(q),
        q.entails(r),
    ensures
        p.entails(r),
{
    entails_apply_auto::<T>();
}

proof fn not_proved_by_contraposition<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.implies(q).satisfied_by(ex),
        not(q).satisfied_by(ex),
    ensures
        not(p).satisfied_by(ex)
{}

proof fn not_eventually_by_always_not<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        always(not(p)).satisfied_by(ex),
    ensures
        not(eventually(p)).satisfied_by(ex),
{
    always_unfold::<T>(ex, not(p));
}

proof fn always_propagate_forwards<T>(ex: Execution<T>, p: TempPred<T>, i: nat)
    requires
        always(p).satisfied_by(ex),
    ensures
        always(p).satisfied_by(ex.suffix(i)),
{
    always_unfold::<T>(ex, p);
    assert forall |j| p.satisfied_by(#[trigger] ex.suffix(i).suffix(j)) by {
        execution_equality::<T>(ex.suffix(i + j), ex.suffix(i).suffix(j));
    };
}

proof fn always_double<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        always(p).satisfied_by(ex),
    ensures
        always(always(p)).satisfied_by(ex),
{
    always_unfold::<T>(ex, p);
    assert forall |i| always(p).satisfied_by(#[trigger] ex.suffix(i)) by {
        always_propagate_forwards::<T>(ex, p, i);
    };
}

proof fn always_to_current<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        always(p).satisfied_by(ex),
    ensures
        p.satisfied_by(ex),
{
    execution_equality::<T>(ex, ex.suffix(0));
}

proof fn always_to_future<T>(ex: Execution<T>, p: TempPred<T>, i: nat)
    requires
        always(p).satisfied_by(ex),
    ensures
        p.satisfied_by(ex.suffix(i))
{
    always_propagate_forwards::<T>(ex, p, i);
    always_to_current::<T>(ex.suffix(i), p);
}

proof fn eventually_propagate_backwards<T>(ex: Execution<T>, p: TempPred<T>, i: nat)
    requires
        eventually(p).satisfied_by(ex.suffix(i)),
    ensures
        eventually(p).satisfied_by(ex),
{
    eventually_unfold::<T>(ex.suffix(i), p);
    let witness_idx = eventually_choose_witness(ex.suffix(i), p);
    execution_equality::<T>(ex.suffix(i).suffix(witness_idx), ex.suffix(i + witness_idx));
}

proof fn eventually_proved_by_witness<T>(ex: Execution<T>, p: TempPred<T>, witness_idx: nat)
    requires
        p.satisfied_by(ex.suffix(witness_idx)),
    ensures
        eventually(p).satisfied_by(ex)
{}

spec fn eventually_choose_witness<T>(ex: Execution<T>, p: TempPred<T>) -> nat
    recommends
        exists |i| p.satisfied_by(#[trigger] ex.suffix(i)),
{
    let witness = choose |i| p.satisfied_by(#[trigger] ex.suffix(i));
    witness
}

proof fn equals_trans<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        p.equals(q).satisfied_by(ex),
        q.equals(r).satisfied_by(ex),
    ensures
        p.equals(r).satisfied_by(ex),
{}

proof fn implies_trans<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        p.implies(q).satisfied_by(ex),
        q.implies(r).satisfied_by(ex),
    ensures
        p.implies(r).satisfied_by(ex),
{}

proof fn equals_to_implies<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.equals(q).satisfied_by(ex),
    ensures
        p.implies(q).satisfied_by(ex),
        q.implies(p).satisfied_by(ex),
{}

proof fn implies_to_equals<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.implies(q).satisfied_by(ex),
        q.implies(p).satisfied_by(ex),
    ensures
        p.equals(q).satisfied_by(ex),
{}

proof fn valid_equals_to_valid_implies<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        valid(p.equals(q)),
    ensures
        valid(p.implies(q)),
        valid(q.implies(p)),
{
    assert forall |ex| p.implies(q).satisfied_by(ex) && q.implies(p).satisfied_by(ex) by {
        equals_to_implies::<T>(ex, p, q);
    };
}

proof fn valid_implies_to_valid_equals<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        valid(p.implies(q)),
        valid(q.implies(p)),
    ensures
        valid(p.equals(q)),
{
    assert forall |ex| p.equals(q).satisfied_by(ex) by {
        implies_to_equals(ex, p, q);
    };
}

proof fn valid_p_implies_always_p<T>(p: TempPred<T>)
    requires
        valid(p),
    ensures
        valid(always(p)),
{
    assert forall |ex| #[trigger] always(p).satisfied_by(ex) by {
        assert(forall |i| #[trigger] p.satisfied_by(ex.suffix(i)));
    };
}

pub proof fn implies_to_leads_to<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(p.implies(q))),
    ensures
        spec.entails(p.leads_to(q)),
{
    assert forall |ex| spec.satisfied_by(ex)
    implies #[trigger] p.leads_to(q).satisfied_by(ex) by {
        implies_apply(ex, spec, always(p.implies(q)));
        always_unfold(ex, p.implies(q));
        assert forall |i: nat| p.satisfied_by(#[trigger] ex.suffix(i))
        implies eventually(q).satisfied_by(ex.suffix(i)) by {
            implies_apply(ex.suffix(i), p, q);
            execution_equality::<T>(ex.suffix(i), ex.suffix(i).suffix(0));
        };
    };
}

proof fn implies_and<T>(p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        valid(p.implies(q)),
        valid(p.implies(r)),
    ensures
        valid(p.implies(q.and(r))),
{
    assert forall |ex| p.satisfied_by(ex) implies #[trigger] q.and(r).satisfied_by(ex) by {
        implies_apply::<T>(ex, p, q);
        implies_apply::<T>(ex, p, r);
    };
}

proof fn always_implies_current<T>(p: TempPred<T>)
    ensures
        valid(always(p).implies(p)),
{
    assert forall |ex| always(p).satisfied_by(ex) implies #[trigger] p.satisfied_by(ex) by {
        always_unfold(ex, p);
        execution_equality::<T>(ex, ex.suffix(0));
    };
}

proof fn always_distributed_by_and<T>(p: TempPred<T>, q: TempPred<T>)
    ensures
        valid(always(p.and(q)).implies(always(p).and(always(q)))),
{
    assert forall |ex| #[trigger] always(p.and(q)).satisfied_by(ex) implies always(p).and(always(q)).satisfied_by(ex) by {
        always_unfold::<T>(ex, p.and(q));
    };
}

proof fn init_invariant_rec<T>(ex: Execution<T>, init: StatePred<T>, next: ActionPred<T>, inv: StatePred<T>, i: nat)
    requires
        init(ex.head()),
        forall |idx: nat| next(#[trigger] ex.suffix(idx).head(), ex.suffix(idx).head_next()),
        forall |idx: nat| init(#[trigger] ex.suffix(idx).head()) ==> inv(ex.suffix(idx).head()),
        forall |idx: nat| inv(#[trigger] ex.suffix(idx).head()) && next(ex.suffix(idx).head(), ex.suffix(idx).head_next())
            ==> inv(ex.suffix(idx).head_next()),
    ensures
        inv(ex.suffix(i).head()),
    decreases
        i,
{
    if i == 0 {
        assert(init(ex.suffix(0).head()));
    } else {
        init_invariant_rec::<T>(ex, init, next, inv, (i-1) as nat);
    }
}

proof fn always_p_or_eventually_q_rec<T>(ex: Execution<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>, i: nat)
    requires
        forall |idx| p.satisfied_by(ex.suffix(idx)) && next.satisfied_by(ex.suffix(idx))
            ==> p.satisfied_by(ex.suffix(idx + 1)) || q.satisfied_by(ex.suffix(idx + 1)),
        forall |idx| next.satisfied_by(#[trigger] ex.suffix(idx)),
        forall |idx| !q.satisfied_by(#[trigger] ex.suffix(idx)),
        p.satisfied_by(ex),
    ensures
        p.satisfied_by(ex.suffix(i)),
    decreases
        i,
{
    if i == 0 {
        execution_equality::<T>(ex, ex.suffix(0));
    } else {
        always_p_or_eventually_q_rec::<T>(ex, next, p, q, (i-1) as nat);
    }
}

proof fn always_p_or_eventually_q<T>(ex: Execution<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        always(p.and(next).implies(later(p).or(later(q)))).satisfied_by(ex),
        always(next).satisfied_by(ex),
    ensures
        always(p.implies(always(p).or(eventually(q)))).satisfied_by(ex),
{
    assert forall |i| p.satisfied_by(#[trigger] ex.suffix(i)) implies
    always(p).satisfied_by(ex.suffix(i)) || eventually(q).satisfied_by(ex.suffix(i)) by {
        always_propagate_forwards::<T>(ex, next, i);
        always_unfold::<T>(ex.suffix(i), next);

        assert forall |idx| p.satisfied_by(#[trigger] ex.suffix(i).suffix(idx)) && next.satisfied_by(ex.suffix(i).suffix(idx))
        implies p.satisfied_by(ex.suffix(i).suffix(idx + 1)) || q.satisfied_by(ex.suffix(i).suffix(idx + 1)) by {
            always_propagate_forwards::<T>(ex, p.and(next).implies(later(p).or(later(q))), i);
            always_propagate_forwards::<T>(ex.suffix(i), p.and(next).implies(later(p).or(later(q))), idx);
            implies_apply::<T>(ex.suffix(i).suffix(idx), p.and(next), later(p).or(later(q)));
            if later(p).satisfied_by(ex.suffix(i).suffix(idx)) {
                later_unfold::<T>(ex.suffix(i).suffix(idx), p);
                execution_equality::<T>(ex.suffix(i).suffix(idx).suffix(1), ex.suffix(i).suffix(idx + 1));
            } else {
                later_unfold::<T>(ex.suffix(i).suffix(idx), q);
                execution_equality::<T>(ex.suffix(i).suffix(idx).suffix(1), ex.suffix(i).suffix(idx + 1));
            }
        };

        if !eventually(q).satisfied_by(ex.suffix(i)) {
            not_eventually_unfold::<T>(ex.suffix(i), q);
            assert forall |j| p.satisfied_by(#[trigger] ex.suffix(i).suffix(j)) by {
                always_p_or_eventually_q_rec::<T>(ex.suffix(i), next, p, q, j);
            };
        }
    };
}

proof fn next_preserves_inv_rec<T>(ex: Execution<T>, next: TempPred<T>, inv: TempPred<T>, i: nat)
    requires
        inv.satisfied_by(ex),
        forall |idx| next.satisfied_by(#[trigger] ex.suffix(idx)),
        forall |idx| inv.satisfied_by(#[trigger] ex.suffix(idx)) && next.satisfied_by(ex.suffix(idx))
            ==> inv.satisfied_by(ex.suffix(idx + 1)),
    ensures
        inv.satisfied_by(ex.suffix(i)),
    decreases
        i,
{
    if i == 0 {
        execution_equality::<T>(ex, ex.suffix(0));
    } else {
        next_preserves_inv_rec::<T>(ex, next, inv, (i-1) as nat);
    }
}

proof fn p_is_preserved_before_t<T>(ex: Execution<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>, t: nat, i: nat)
    requires
        i <= t,
        p.satisfied_by(ex),
        forall |idx: nat| next.satisfied_by(#[trigger] ex.suffix(idx)),
        forall |idx: nat| idx < t ==> !q.satisfied_by(#[trigger] ex.suffix(idx)),
        forall |idx: nat| p.satisfied_by(ex.suffix(idx)) && !q.satisfied_by(ex.suffix(idx)) && next.satisfied_by(#[trigger] ex.suffix(idx))
            ==> p.satisfied_by(ex.suffix(idx + 1)),
    ensures
        p.satisfied_by(ex.suffix(i)),
    decreases
        i,
{
    if i == 0 {
        execution_equality::<T>(ex, ex.suffix(0));
    } else {
        p_is_preserved_before_t::<T>(ex, next, p, q, t, (i-1) as nat);
    }
}

proof fn confluence_at_some_point<T>(ex: Execution<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>, i: nat)
    requires
        p.satisfied_by(ex),
        q.satisfied_by(ex.suffix(i)),
        always(p.and(not(q)).and(next).implies(later(p))).satisfied_by(ex),
        always(next).satisfied_by(ex),
    ensures
        exists |idx: nat| p.and(q).satisfied_by(#[trigger] ex.suffix(idx)),
    decreases
        i,
{
    if i == 0 {
        execution_equality::<T>(ex, ex.suffix(0));
        assert(p.and(q).satisfied_by(ex.suffix(0)));
    } else {
        if exists |j: nat| {
            &&& j < i
            &&& q.satisfied_by(#[trigger] ex.suffix(j))
        } {
            let t = choose |j: nat| {
                &&& j < i
                &&& q.satisfied_by(#[trigger] ex.suffix(j))
            };
            confluence_at_some_point::<T>(ex, next, p, q, t);
        } else {
            assert forall |idx: nat| p.satisfied_by(ex.suffix(idx)) && !q.satisfied_by(ex.suffix(idx)) && next.satisfied_by(#[trigger] ex.suffix(idx))
            implies p.satisfied_by(ex.suffix(idx + 1)) by {
                always_unfold::<T>(ex, p.and(not(q)).and(next).implies(later(p)));
                implies_apply::<T>(ex.suffix(idx), p.and(not(q)).and(next), later(p));
                execution_equality::<T>(ex.suffix(idx).suffix(1), ex.suffix(idx + 1));
            };
            p_is_preserved_before_t::<T>(ex, next, p, q, i, i);
            assert(p.and(q).satisfied_by(ex.suffix(i)));
        }
    }
}

/// All the lemmas above are used internally for proving the lemmas below
/// The following lemmas are used by developers to simplify liveness/safety proof

/// Predict future behavior from always predicate
/// pre:
///     spec(p)
///     spec |= always(p)
/// post:
///     p(ex.suffix(i))
pub proof fn instantiate_entailed_always<T>(ex: Execution<T>, i: nat, spec: TempPred<T>, p: TempPred<T>)
    requires
        spec.satisfied_by(ex),
        spec.implies(always(p)).satisfied_by(ex),
    ensures
        p.satisfied_by(ex.suffix(i)),
{
    implies_apply::<T>(ex, spec, always(p));
    always_unfold::<T>(ex, p);
}

pub proof fn instantiate_entailed_leads_to<T>(ex: Execution<T>, i: nat, spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.satisfied_by(ex),
        spec.implies(p.leads_to(q)).satisfied_by(ex),
    ensures
        p.implies(eventually(q)).satisfied_by(ex.suffix(i)),
{
    implies_apply::<T>(ex, spec, p.leads_to(q));
    leads_to_unfold::<T>(ex, p, q);
}

pub proof fn execution_equality<T>(ex1: Execution<T>, ex2: Execution<T>)
    requires
        forall |i: nat| #[trigger] (ex1.nat_to_state)(i) == (ex2.nat_to_state)(i),
    ensures
        ex1 == ex2,
{
    fun_ext::<nat, T>(ex1.nat_to_state, ex2.nat_to_state);
}

pub proof fn temp_pred_equality<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        valid(p.equals(q)),
    ensures
        p == q,
{
    assert forall |ex: Execution<T>| #[trigger] (p.pred)(ex) == (q.pred)(ex) by {
        valid_equals_to_valid_implies::<T>(p, q);
        if (p.pred)(ex) {
            implies_apply::<T>(ex, p, q);
        } else {
            implies_contraposition_apply::<T>(ex, q, p);
        }
    };
    fun_ext::<Execution<T>, bool>(p.pred, q.pred);
}

pub proof fn always_and_equality<T>(p: TempPred<T>, q: TempPred<T>)
    ensures
        always(p.and(q)) == always(p).and(always(q)),
{
    assert forall |ex| #[trigger] always(p.and(q)).satisfied_by(ex) implies always(p).and(always(q)).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) by {
            always_unfold::<T>(ex, p.and(q));
        }
        assert(always(p).satisfied_by(ex));
        assert forall |i| #[trigger] q.satisfied_by(ex.suffix(i)) by {
            always_unfold::<T>(ex, p.and(q));
        }
        assert(always(q).satisfied_by(ex));
    };
    temp_pred_equality::<T>(always(p.and(q)), always(p).and(always(q)));
}

pub proof fn p_and_always_p_equals_always_p<T>(p: TempPred<T>)
    ensures
        p.and(always(p)) == always(p),
{
    assert forall |ex| #[trigger] always(p).satisfied_by(ex) implies p.and(always(p)).satisfied_by(ex) by {
        always_to_current::<T>(ex, p);
    };
    temp_pred_equality::<T>(p.and(always(p)), always(p));
}

pub proof fn a_to_temp_pred_equality<T, A>(p: FnSpec(A) -> TempPred<T>, q: FnSpec(A) -> TempPred<T>)
    requires
        forall |a: A| #[trigger] valid(p(a).equals(q(a))),
    ensures
        p == q,
{
    assert forall |a: A| #[trigger] p(a) == q(a) by {
        temp_pred_equality::<T>(p(a), q(a));
    };
    fun_ext::<A, TempPred<T>>(p, q);
}

pub proof fn tla_exists_equality<T, A>(f: FnSpec(A, T) -> bool)
    ensures
        lift_state(|t| exists |a| #[trigger] f(a, t)) == tla_exists(|a| lift_state(|t| f(a, t))),
{
    let p = lift_state(|t| exists |a| #[trigger] f(a, t));
    let q = tla_exists(|a| lift_state(|t| f(a, t)));

    let partial_p = |t| exists |a| #[trigger] f(a, t);
    let partial_q = |a| lift_state(|t| f(a, t));
    assert forall |ex| p.satisfied_by(ex) implies q.satisfied_by(ex) by {
        assert(partial_p(ex.head()));
        assert(exists |a| #[trigger] f(a, ex.head()));
        let witness_a = choose |a| #[trigger] f(a, ex.head());
        assert(partial_q(witness_a).satisfied_by(ex));
    };

    temp_pred_equality::<T>(p, q);
}

/// Lift the "always" outside tla_forall if the function is previously wrapped by an "always"
/// Note: Verus may not able to infer that (|a| func(a))(a) equals func(a).
///       Please turn to lemma tla_forall_always_equality_variant for troubleshooting. 
pub proof fn tla_forall_always_equality<T, A>(a_to_p: FnSpec(A) -> TempPred<T>)
    ensures
        tla_forall(|a: A| always(a_to_p(a))) == always(tla_forall(a_to_p)),
{
    let a_to_always_p = |a: A| always(a_to_p(a));

    assert forall |ex| #[trigger] tla_forall(a_to_always_p).satisfied_by(ex)
    implies always(tla_forall(a_to_p)).satisfied_by(ex) by {
        assert forall |i| #[trigger] tla_forall(a_to_p).satisfied_by(ex.suffix(i)) by {
            assert forall |a| #[trigger] a_to_p(a).satisfied_by(ex.suffix(i)) by {
                tla_forall_unfold::<T, A>(ex, a_to_always_p);
                assert(a_to_always_p(a).satisfied_by(ex));
                always_unfold::<T>(ex, a_to_p(a));
            };
        };
    };

    assert forall |ex| #[trigger] always(tla_forall(a_to_p)).satisfied_by(ex)
    implies tla_forall(a_to_always_p).satisfied_by(ex) by {
        assert forall |a| #[trigger] a_to_always_p(a).satisfied_by(ex) by {
            assert forall |i| #[trigger] a_to_p(a).satisfied_by(ex.suffix(i)) by {
                always_unfold::<T>(ex, tla_forall(a_to_p));
                tla_forall_unfold::<T, A>(ex.suffix(i), a_to_p);
            };
        };
    };

    temp_pred_equality::<T>(tla_forall(|a: A| always(a_to_p(a))), always(tla_forall(a_to_p)));
}

pub proof fn tla_forall_always_equality_variant<T, A>(a_to_always: FnSpec(A) -> TempPred<T>, a_to_p: FnSpec(A) -> TempPred<T>)
    requires
        forall |a: A| #![trigger a_to_always(a)] valid(a_to_always(a).equals((|a: A| always(a_to_p(a)))(a))),
    ensures
        tla_forall(a_to_always) == always(tla_forall(a_to_p)),
{
    a_to_temp_pred_equality::<T, A>(a_to_always, |a: A| always(a_to_p(a)));
    temp_pred_equality::<T>(tla_forall(a_to_always), tla_forall(|a: A| always(a_to_p(a))));
    tla_forall_always_equality::<T, A>(a_to_p);
}

pub proof fn tla_forall_not_equality<T, A>(a_to_p: FnSpec(A) -> TempPred<T>)
    ensures
        tla_forall(|a: A| not(a_to_p(a))) == not(tla_exists(a_to_p)),
{
    let a_to_not_p = |a: A| not(a_to_p(a));
    assert forall |ex| #[trigger] tla_forall(a_to_not_p).satisfied_by(ex)
    implies not(tla_exists(a_to_p)).satisfied_by(ex) by {
        assert forall |a| !#[trigger] a_to_p(a).satisfied_by(ex) by {
            tla_forall_unfold::<T, A>(ex, a_to_not_p);
            assert(a_to_not_p(a).satisfied_by(ex));
        };
    };

    temp_pred_equality::<T>(tla_forall(|a: A| not(a_to_p(a))), not(tla_exists(a_to_p)));
}

pub proof fn tla_forall_and_equality<T, A>(a_to_p: FnSpec(A) -> TempPred<T>, q: TempPred<T>)
    ensures
        tla_forall(|a: A| a_to_p(a).and(q)) == tla_forall(a_to_p).and(q),
{
    let a_to_p_and_q = |a: A| a_to_p(a).and(q);
    assert forall |ex| #[trigger] tla_forall(a_to_p_and_q).satisfied_by(ex)
    implies (tla_forall(a_to_p).and(q)).satisfied_by(ex) by {
        tla_forall_unfold::<T, A>(ex, a_to_p_and_q);
        // Now we unfold it to:
        // forall |a| a_to_p(a).and(q).satisfied_by(ex)
        // Use assert forall block to prove tla_forall(a_to_p).satisfied_by(ex)
        assert forall |a| #[trigger] a_to_p(a).satisfied_by(ex) by {
            assert(a_to_p_and_q(a).satisfied_by(ex));
        };
        // Use arbitrary() to instantiate the above forall to prove q.satisfied_by(ex)
        assert(a_to_p_and_q(arbitrary()).satisfied_by(ex));
    };

    temp_pred_equality::<T>(tla_forall(|a: A| a_to_p(a).and(q)), tla_forall(a_to_p).and(q));
}

pub proof fn tla_forall_apply<T, A>(a_to_p: FnSpec(A) -> TempPred<T>, a: A)
    ensures
        tla_forall(a_to_p).entails(a_to_p(a)),
{
    assert forall |ex| #[trigger] tla_forall(a_to_p).satisfied_by(ex) implies a_to_p(a).satisfied_by(ex) by {
        tla_forall_unfold::<T, A>(ex, a_to_p);
    }
}

pub proof fn tla_forall_or_equality<T, A>(a_to_p: FnSpec(A) -> TempPred<T>, q: TempPred<T>)
    ensures
        tla_forall(|a: A| a_to_p(a).or(q)) == tla_forall(a_to_p).or(q),
{
    let a_to_p_or_q = |a: A| a_to_p(a).or(q);
    assert forall |ex| #[trigger] tla_forall(a_to_p_or_q).satisfied_by(ex)
    implies (tla_forall(a_to_p).or(q)).satisfied_by(ex) by {
        tla_forall_unfold::<T, A>(ex, a_to_p_or_q);
        if !q.satisfied_by(ex) {
            assert forall |a| #[trigger] a_to_p(a).satisfied_by(ex) by {
                assert(a_to_p_or_q(a).satisfied_by(ex));
            };
        }
    };

    temp_pred_equality::<T>(tla_forall(|a: A| a_to_p(a).or(q)), tla_forall(a_to_p).or(q));
}

pub proof fn tla_exists_and_equality<T, A>(a_to_p: FnSpec(A) -> TempPred<T>, q: TempPred<T>)
    ensures
        tla_exists(|a: A| a_to_p(a).and(q)) == tla_exists(a_to_p).and(q),
{
    let a_to_p_and_q = |a: A| a_to_p(a).and(q);
    assert forall |ex| #[trigger] (tla_exists(a_to_p).and(q)).satisfied_by(ex)
    implies tla_exists(a_to_p_and_q).satisfied_by(ex) by {
        let witness_a = tla_exists_choose_witness::<T, A>(ex, a_to_p);
        tla_exists_proved_by_witness::<T, A>(ex, a_to_p_and_q, witness_a);
    };

    temp_pred_equality::<T>(tla_exists(|a: A| a_to_p(a).and(q)), tla_exists(a_to_p).and(q));
}

pub proof fn tla_exists_or_equality<T, A>(a_to_p: FnSpec(A) -> TempPred<T>, q: TempPred<T>)
    ensures
        tla_exists(|a: A| a_to_p(a).or(q)) == tla_exists(a_to_p).or(q),
{
    let a_to_p_or_q = |a: A| a_to_p(a).or(q);
    assert forall |ex| #[trigger] (tla_exists(a_to_p).or(q)).satisfied_by(ex)
    implies tla_exists(a_to_p_or_q).satisfied_by(ex) by {
        if !q.satisfied_by(ex) {
            let witness_a = tla_exists_choose_witness::<T, A>(ex, a_to_p);
            tla_exists_proved_by_witness::<T, A>(ex, a_to_p_or_q, witness_a);
        } else {
            assert(a_to_p_or_q(arbitrary()).satisfied_by(ex));
        }
    };

    temp_pred_equality::<T>(tla_exists(|a: A| a_to_p(a).or(q)), tla_exists(a_to_p).or(q));
}

pub proof fn tla_forall_implies_equality1<T, A>(a_to_p: FnSpec(A) -> TempPred<T>, q: TempPred<T>)
    ensures
        tla_forall(|a: A| a_to_p(a).implies(q)) == tla_exists(a_to_p).implies(q),
{
    let a_to_not_p = |a: A| not(a_to_p(a));
    a_to_temp_pred_equality::<T, A>(|a: A| a_to_p(a).implies(q), |a: A| a_to_not_p(a).or(q));
    temp_pred_equality::<T>(tla_forall(|a: A| a_to_p(a).implies(q)), tla_forall(|a: A| a_to_not_p(a).or(q)));
    tla_forall_or_equality::<T, A>(a_to_not_p, q);
    tla_forall_not_equality::<T, A>(a_to_p);
    temp_pred_equality::<T>(not(tla_exists(a_to_p)).or(q), tla_exists(a_to_p).implies(q));
}

pub proof fn tla_forall_implies_equality2<T, A>(p: TempPred<T>, a_to_q: FnSpec(A) -> TempPred<T>)
    ensures
        tla_forall(|a: A| p.implies(a_to_q(a))) == p.implies(tla_forall(a_to_q)),
{
    a_to_temp_pred_equality::<T, A>(|a: A| p.implies(a_to_q(a)), |a: A| a_to_q(a).or(not(p)));
    temp_pred_equality::<T>(tla_forall(|a: A| p.implies(a_to_q(a))), tla_forall(|a: A| a_to_q(a).or(not(p))));
    tla_forall_or_equality::<T, A>(a_to_q, not(p));
    temp_pred_equality::<T>(tla_forall(a_to_q).or(not(p)), p.implies(tla_forall(a_to_q)));
}

pub proof fn tla_exists_implies_equality1<T, A>(p: TempPred<T>, a_to_q: FnSpec(A) -> TempPred<T>)
    ensures
        tla_exists(|a: A| p.implies(a_to_q(a))) == p.implies(tla_exists(a_to_q)),
{
    a_to_temp_pred_equality::<T, A>(|a: A| p.implies(a_to_q(a)), |a: A| a_to_q(a).or(not(p)));
    temp_pred_equality::<T>(tla_exists(|a: A| p.implies(a_to_q(a))), tla_exists(|a: A| a_to_q(a).or(not(p))));
    tla_exists_or_equality::<T, A>(a_to_q, not(p));
    temp_pred_equality::<T>(tla_exists(a_to_q).or(not(p)), p.implies(tla_exists(a_to_q)));
}

pub proof fn tla_forall_leads_to_equality1<T, A>(a_to_p: FnSpec(A) -> TempPred<T>, q: TempPred<T>)
    ensures
        tla_forall(|a: A| a_to_p(a).leads_to(q)) == tla_exists(a_to_p).leads_to(q),
{
    tla_forall_always_equality_variant::<T, A>(|a: A| a_to_p(a).leads_to(q), |a: A| a_to_p(a).implies(eventually(q)));
    tla_forall_implies_equality1::<T, A>(a_to_p, eventually(q));
}

pub proof fn tla_forall_always_implies_equality2<T, A>(p: TempPred<T>, a_to_q: FnSpec(A) -> TempPred<T>)
    ensures
        tla_forall(|a: A| always(p.implies(a_to_q(a)))) == always(p.implies(tla_forall(a_to_q))),
{
    tla_forall_always_equality_variant::<T, A>(|a: A| always(p.implies(a_to_q(a))), |a: A| p.implies(a_to_q(a)));
    tla_forall_implies_equality2::<T, A>(p, a_to_q);
}

pub proof fn spec_entails_tla_forall<T, A>(spec: TempPred<T>, a_to_p: FnSpec(A) -> TempPred<T>)
    requires
        forall |a: A| spec.entails(#[trigger] a_to_p(a)),
    ensures
        spec.entails(tla_forall(a_to_p)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies tla_forall(a_to_p).satisfied_by(ex) by {
        assert forall |a| #[trigger] a_to_p(a).satisfied_by(ex) by {
            implies_apply::<T>(ex, spec, a_to_p(a));
        };
    };
}

pub proof fn always_implies_forall_intro<T, A>(spec: TempPred<T>, p: TempPred<T>, a_to_q: FnSpec(A) -> TempPred<T>)
    requires
        forall |a: A| #[trigger] spec.entails(always(p.implies(a_to_q(a)))),
    ensures
        spec.entails(always(p.implies(tla_forall(a_to_q)))),
{
    let a_to_always_p_implies_q = |a: A| always(p.implies(a_to_q(a)));
    spec_entails_tla_forall::<T, A>(spec, a_to_always_p_implies_q);
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(p.implies(tla_forall(a_to_q))).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, tla_forall(a_to_always_p_implies_q));
        tla_forall_always_implies_equality2::<T, A>(p, a_to_q)
    };
}

pub proof fn leads_to_exists_intro<T, A>(spec: TempPred<T>, a_to_p: FnSpec(A) -> TempPred<T>, q: TempPred<T>)
    requires
        forall |a: A| #[trigger] spec.entails(a_to_p(a).leads_to(q)),
    ensures
        spec.entails(tla_exists(a_to_p).leads_to(q)),
{
    let a_to_p_leads_to_q = |a: A| a_to_p(a).leads_to(q);
    spec_entails_tla_forall::<T, A>(spec, a_to_p_leads_to_q);
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies tla_exists(a_to_p).leads_to(q).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, tla_forall(a_to_p_leads_to_q));
        tla_forall_leads_to_equality1::<T, A>(a_to_p, q);
    };
}

/// This lemmas instantiates tla_forall for a.
pub proof fn use_tla_forall<T, A>(spec: TempPred<T>, a_to_p: FnSpec(A) -> TempPred<T>, a: A)
    requires
        spec.entails(tla_forall(a_to_p)),
    ensures
        spec.entails(a_to_p(a)),
{
    entails_apply_auto::<T>();
    assert forall |ex: Execution<T>| #[trigger] spec.implies(a_to_p(a)).satisfied_by(ex) by {
        assert(spec.implies(tla_forall(a_to_p)).satisfied_by(ex));
    };
}

/// Obviously p ~> p is valid
/// post:
///     |= p ~> p
pub proof fn leads_to_self_temp<T>(p: TempPred<T>)
    ensures
        valid(p.leads_to(p)),
{
    assert forall |ex| #[trigger] always(p.implies(eventually(p))).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(p).satisfied_by(ex.suffix(i)) by {
            execution_equality::<T>(ex.suffix(i), ex.suffix(i).suffix(0));
            eventually_proved_by_witness::<T>(ex.suffix(i), p, 0);
        };
    };
}

/// StatePred version of leads_to_self_temp
pub proof fn leads_to_self<T>(p: StatePred<T>)
    ensures
        valid(lift_state(p).leads_to(lift_state(p))),
{
    leads_to_self_temp::<T>(lift_state(p));
}

/// Entails p and q if entails each of them.
/// pre:
///     spec |= p
///     spec |= q
/// post:
///     spec |= p && q
pub proof fn entails_and_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(p),
        spec.entails(q),
    ensures
        spec.entails(p.and(q)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.and(q).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, p);
        implies_apply::<T>(ex, spec, q);
    };
}

/// The three-predicate-version for entails_and_temp
pub proof fn entails_and_3_temp<T>(spec: TempPred<T>, p1: TempPred<T>, p2: TempPred<T>, p3: TempPred<T>)
    requires
        spec.entails(p1),
        spec.entails(p2),
        spec.entails(p3),
    ensures
        spec.entails(p1.and(p2).and(p3)),
{
    entails_and_temp::<T>(spec, p1, p2);
    entails_and_temp::<T>(spec, p1.and(p2), p3);
}

/// The four-predicate-version for entails_and_temp
pub proof fn entails_and_4_temp<T>(spec: TempPred<T>, p1: TempPred<T>, p2: TempPred<T>, p3: TempPred<T>, p4: TempPred<T>)
    requires
        spec.entails(p1),
        spec.entails(p2),
        spec.entails(p3),
        spec.entails(p4),
    ensures
        spec.entails(p1.and(p2).and(p3).and(p4)),
{
    entails_and_3_temp::<T>(spec, p1, p2, p3);
    entails_and_temp::<T>(spec, p1.and(p2).and(p3), p4);
}

/// Combining two specs together entails p and q if each of them entails p, q respectively.
/// pre:
///     spec1 |= p
///     spec2 |= q
/// post:
///     spec1 /\ spec2 |= p /\ q
pub proof fn entails_and_different_temp<T>(spec1: TempPred<T>, spec2: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec1.entails(p),
        spec2.entails(q),
    ensures
        spec1.and(spec2).entails(p.and(q)),
{
    assert forall |ex| #[trigger] spec1.and(spec2).satisfied_by(ex) implies p.and(q).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec1, p);
        implies_apply::<T>(ex, spec2, q);
    };
}

/// An always predicate is stable.
/// post:
///     |= stable(always(p))
pub proof fn always_p_stable<T>(p: TempPred<T>)
    ensures
        valid(stable(always(p))),
{
    assert forall |ex| #[trigger] always(p).satisfied_by(ex) implies always(always(p)).satisfied_by(ex) by {
        assert forall |i| #[trigger] always(p).satisfied_by(ex.suffix(i)) by {
            always_propagate_forwards::<T>(ex, p, i);
        }
    }
}

/// p and q is stable if both p and q are stable.
/// pre:
///     |= stable(p)
///     |= stable(q)
/// post:
///     |= stable(p /\ q)
pub proof fn stable_and_temp<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        valid(stable(p)),
        valid(stable(q)),
    ensures
        valid(stable(p.and(q))),
{
    assert forall |ex| #[trigger] p.and(q).satisfied_by(ex) implies always(p.and(q)).satisfied_by(ex) by {
        stable_unfold::<T>(ex, p);
        stable_unfold::<T>(ex, q);
    }
}

/// The three-predicate-version of stable_and_temp
/// This is created for avoid multiple calls to stable_and_temp.
pub proof fn stable_and_3_temp<T>(p1: TempPred<T>, p2: TempPred<T>, p3: TempPred<T>)
    requires
        valid(stable(p1)),
        valid(stable(p2)),
        valid(stable(p3)),
    ensures
        valid(stable(p1.and(p2).and(p3))),
{
    stable_and_temp::<T>(p1, p2);
    stable_and_temp::<T>(p1.and(p2), p3);
}

/// The four-predicate-version of stable_and_temp
pub proof fn stable_and_4_temp<T>(p1: TempPred<T>, p2: TempPred<T>, p3: TempPred<T>, p4: TempPred<T>)
    requires
        valid(stable(p1)),
        valid(stable(p2)),
        valid(stable(p3)),
        valid(stable(p4)),
    ensures
        valid(stable(p1.and(p2).and(p3).and(p4))),
{
    stable_and_temp::<T>(p1, p2);
    stable_and_3_temp::<T>(p1.and(p2), p3, p4);
}

/// Unpack the assumption from left to the right side of |=
/// pre:
///     |= stable(partial_spec)
///     partial_spec /\ asm |= True ~> p
/// post:
///     init /\ partial_spec |= asm ~> p
/// TODO: discuss how to prove "safety" invariants that depend on asm
pub proof fn unpack_assumption_from_spec<T>(init: TempPred<T>, partial_spec: TempPred<T>, asm: TempPred<T>, p: TempPred<T>)
    requires
        valid(stable(partial_spec)),
        partial_spec.and(asm).entails(true_pred().leads_to(p)),
    ensures
        init.and(partial_spec).entails(asm.leads_to(p)),
{
    assert forall |ex| #[trigger] init.and(partial_spec).satisfied_by(ex) implies asm.leads_to(p).satisfied_by(ex) by {
        assert forall |i| #[trigger] asm.satisfied_by(ex.suffix(i)) implies eventually(p).satisfied_by(ex.suffix(i)) by {
            stable_unfold::<T>(ex, partial_spec);
            implies_apply::<T>(ex.suffix(i), partial_spec.and(asm), true_pred().leads_to(p));
            leads_to_unfold::<T>(ex.suffix(i), true_pred(), p);
            execution_equality::<T>(ex.suffix(i), ex.suffix(i).suffix(0));
            implies_apply::<T>(ex.suffix(i), true_pred(), eventually(p));
        };
    };
}

/// A stronger spec can undoubtedly entail the previous conclusion.
/// pre:
///     spec |= p
/// post:
///     spec /\ asm |= p
pub proof fn strengthen_spec<T>(spec: TempPred<T>, asm: TempPred<T>, p: TempPred<T>)
    requires
        spec.entails(p),
    ensures
        (spec.and(asm)).entails(p),
{
    assert forall |ex| #[trigger] (spec.and(asm)).satisfied_by(ex) implies p.satisfied_by(ex) by {
        assert(spec.satisfied_by(ex));
        entails_apply(ex, spec, p);
    };
}

/// This lemma is used to make the predicate as concise as possible.
/// Similar to the first-order logic where p equals p /\ q when p -> q is satisfied,
/// we can reduce the size of predicate when some part of it implies the rest.
pub proof fn simplify_predicate<T>(simpler: TempPred<T>, redundant: TempPred<T>)
    requires
        simpler.entails(redundant),
    ensures
        simpler == simpler.and(redundant),
{
    assert forall |ex| #[trigger] simpler.satisfied_by(ex) implies simpler.and(redundant).satisfied_by(ex) by {
        entails_and_temp::<T>(simpler, simpler, redundant);
        entails_apply::<T>(ex, simpler, simpler.and(redundant));
    };
    temp_pred_equality::<T>(simpler, simpler.and(redundant));
}


/// Prove safety by induction.
/// pre:
///     |= init => inv
///     |= inv /\ next => inv'
///     spec |= init /\ []next
/// post:
///     spec |= []inv
pub proof fn init_invariant<T>(spec: TempPred<T>, init: StatePred<T>, next: ActionPred<T>, inv: StatePred<T>)
    requires
        forall |s: T| #[trigger] init(s) ==> inv(s),
        forall |s, s_prime: T| inv(s) && #[trigger] next(s, s_prime) ==> inv(s_prime),
        spec.entails(lift_state(init)),
        spec.entails(always(lift_action(next))),
    ensures
        spec.entails(always(lift_state(inv))),
{
    assert forall |ex: Execution<T>| spec.satisfied_by(ex)
    implies #[trigger] always(lift_state(inv)).satisfied_by(ex) by {
        implies_apply(ex, spec, lift_state(init));
        implies_apply(ex, spec, always(lift_action(next)));
        always_unfold::<T>(ex, lift_action(next));
        assert forall |i: nat| inv(#[trigger] ex.suffix(i).head()) by {
            init_invariant_rec(ex, init, next, inv, i);
        };
    };
}

/// Strengthen next with inv.
/// pre:
///     spec |= []next
///     spec |= []inv
///     |= next /\ inv <=> next_and_inv
/// post:
///     spec |= []next_and_inv
pub proof fn strengthen_next<T>(spec: TempPred<T>, next: ActionPred<T>, inv: StatePred<T>, next_and_inv: ActionPred<T>)
    requires
        spec.entails(always(lift_action(next))),
        spec.entails(always(lift_state(inv))),
        valid(lift_action(next_and_inv).equals(lift_action(next).and(lift_state(inv)))),
    ensures
        spec.entails(always(lift_action(next_and_inv))),
{
    entails_and_temp::<T>(spec, always(lift_action(next)), always(lift_state(inv)));
    always_and_equality::<T>(lift_action(next), lift_state(inv));
    temp_pred_equality::<T>(lift_action(next_and_inv), lift_action(next).and(lift_state(inv)));
}

/// Get the initial leads_to.
/// pre:
///     spec |= [](p /\ next => p' /\ q')
///     spec |= [](p /\ next /\ forward => q')
///     spec |= []next
///     spec |= []p ~> forward
/// post:
///     spec |= p ~> q
pub proof fn wf1_variant_temp<T>(spec: TempPred<T>, next: TempPred<T>, forward: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(p.and(next).implies(later(p).or(later(q))))),
        spec.entails(always(p.and(next).and(forward).implies(later(q)))),
        spec.entails(always(next)),
        spec.entails(always(p).leads_to(forward)),
    ensures
        spec.entails(p.leads_to(q)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(q).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i))
        implies eventually(q).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, always(next));
            implies_apply::<T>(ex, spec, always(p.and(next).implies(later(p).or(later(q)))));
            implies_apply::<T>(ex, spec, always(p.and(next).and(forward).implies(later(q))));

            always_p_or_eventually_q::<T>(ex, next, p, q);
            implies_apply::<T>(ex.suffix(i), p, always(p).or(eventually(q)));
            if always(p).satisfied_by(ex.suffix(i)) {
                implies_apply::<T>(ex, spec, always(p).leads_to(forward));
                leads_to_unfold::<T>(ex, always(p), forward);
                implies_apply::<T>(ex.suffix(i), always(p), eventually(forward));
                let witness_idx = eventually_choose_witness::<T>(ex.suffix(i), forward);

                always_propagate_forwards::<T>(ex, next, i);
                always_propagate_forwards::<T>(ex, p.and(next).and(forward).implies(later(q)), i);
                implies_apply::<T>(ex.suffix(i).suffix(witness_idx), p.and(next).and(forward), later(q));
                execution_equality::<T>(ex.suffix(i).suffix(witness_idx).suffix(1), ex.suffix(i).suffix(witness_idx + 1));

                eventually_proved_by_witness::<T>(ex.suffix(i), q, witness_idx+1);
            }
        }
    }
}

/// Get the initial leads_to by assuming always asm.
/// pre:
///     spec |= [](p /\ next /\ asm => p' /\ q')
///     spec |= [](p /\ next /\ forward => q')
///     spec |= []next
///     spec |= []p ~> forward
/// post:
///     spec |= p /\ []asm ~> q
pub proof fn wf1_variant_assume_temp<T>(spec: TempPred<T>, next: TempPred<T>, forward: TempPred<T>, asm: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(p.and(next).and(asm).implies(later(p).or(later(q))))),
        spec.entails(always(p.and(next).and(forward).implies(later(q)))),
        spec.entails(always(next)),
        spec.entails(always(p).leads_to(forward)),
    ensures
        spec.entails(p.and(always(asm)).leads_to(q)),
{
    let p_and_always_asm = p.and(always(asm));

    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(p_and_always_asm.and(next).implies(later(p_and_always_asm).or(later(q)))).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, always(p.and(next).and(asm).implies(later(p).or(later(q)))));
        assert forall |i| #[trigger] p_and_always_asm.and(next).satisfied_by(ex.suffix(i))
        implies later(p_and_always_asm).or(later(q)).satisfied_by(ex.suffix(i)) by {
            always_unfold::<T>(ex.suffix(i), asm);
            execution_equality::<T>(ex.suffix(i), ex.suffix(i).suffix(0));
            implies_apply::<T>(ex.suffix(i), p.and(next).and(asm), later(p).or(later(q)));
            always_propagate_forwards::<T>(ex.suffix(i), asm, 1);
        };
    };

    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(p_and_always_asm.and(next).and(forward).implies(later(q))).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, always(p.and(next).and(forward).implies(later(q))));
        assert forall |i| #[trigger] p_and_always_asm.and(next).and(forward).satisfied_by(ex.suffix(i))
        implies later(q).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex.suffix(i), p.and(next).and(forward), later(q));
        };
    };

    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(p_and_always_asm).leads_to(forward).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, always(p).leads_to(forward));
        leads_to_unfold::<T>(ex, always(p), forward);
        assert forall |i| #[trigger] always(p_and_always_asm).satisfied_by(ex.suffix(i))
        implies eventually(forward).satisfied_by(ex.suffix(i)) by {
            always_unfold::<T>(ex.suffix(i), p_and_always_asm);
            implies_apply::<T>(ex.suffix(i), always(p), eventually(forward));
        };
    };

    wf1_variant_temp::<T>(spec, next, forward, p_and_always_asm, q);
}

/// Get the initial leads_to with a stronger wf assumption than wf1_variant.
/// pre:
///     |= p /\ next => p' /\ q'
///     |= p /\ next /\ forward => q'
///     |= p => enabled(forward)
///     spec |= []next
///     spec |= wf(forward)
/// post:
///     spec |= p ~> q
pub proof fn wf1<T>(spec: TempPred<T>, next: ActionPred<T>, forward: ActionPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        forall |s, s_prime: T| p(s) && #[trigger] next(s, s_prime) ==> p(s_prime) || q(s_prime),
        forall |s, s_prime: T| p(s) && #[trigger] next(s, s_prime) && forward(s, s_prime) ==> q(s_prime),
        forall |s: T| #[trigger] p(s) ==> enabled(forward)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(weak_fairness(forward)),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(lift_state(p)).leads_to(lift_action(forward)).satisfied_by(ex) by {
        assert forall |i| #[trigger] always(lift_state(p)).satisfied_by(ex.suffix(i)) implies eventually(lift_action(forward)).satisfied_by(ex.suffix(i)) by {
            assert(always(lift_state(p).implies(lift_state(enabled(forward)))).satisfied_by(ex.suffix(i)));
            implies_apply_with_always::<T>(ex.suffix(i), lift_state(p), lift_state(enabled(forward)));
            execution_equality::<T>(ex.suffix(i).suffix(0), ex.suffix(i));

            implies_apply::<T>(ex, spec, weak_fairness(forward));
            weak_fairness_unfold::<T>(ex, forward);
            implies_apply::<T>(ex.suffix(i), lift_state(enabled(forward)), eventually(lift_action(forward)));
        };
    };
    wf1_variant_temp::<T>(spec, lift_action(next), lift_action(forward), lift_state(p), lift_state(q));
}

/// Get the initial leads_to by assuming (1) always asm and (2) a stronger wf assumption than wf1_variant_assume.
/// pre:
///     |= p /\ next /\ asm => p' /\ q'
///     |= p /\ next /\ forward => q'
///     |= p => enabled(forward)
///     spec |= []next
///     spec |= wf(forward)
/// post:
///     spec |= p /\ []asm ~> q
pub proof fn wf1_assume<T>(spec: TempPred<T>, next: ActionPred<T>, forward: ActionPred<T>, asm: StatePred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        forall |s, s_prime: T| p(s) && #[trigger] next(s, s_prime) && asm(s) ==> p(s_prime) || q(s_prime),
        forall |s, s_prime: T| p(s) && #[trigger] next(s, s_prime) && forward(s, s_prime) ==> q(s_prime),
        forall |s: T| #[trigger] p(s) ==> enabled(forward)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(weak_fairness(forward)),
    ensures
        spec.entails(lift_state(p).and(always(lift_state(asm))).leads_to(lift_state(q))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(lift_state(p)).leads_to(lift_action(forward)).satisfied_by(ex) by {
        assert forall |i| #[trigger] always(lift_state(p)).satisfied_by(ex.suffix(i)) implies eventually(lift_action(forward)).satisfied_by(ex.suffix(i)) by {
            assert(always(lift_state(p).implies(lift_state(enabled(forward)))).satisfied_by(ex.suffix(i)));
            implies_apply_with_always::<T>(ex.suffix(i), lift_state(p), lift_state(enabled(forward)));
            execution_equality::<T>(ex.suffix(i).suffix(0), ex.suffix(i));

            implies_apply::<T>(ex, spec, weak_fairness(forward));
            weak_fairness_unfold::<T>(ex, forward);
            implies_apply::<T>(ex.suffix(i), lift_state(enabled(forward)), eventually(lift_action(forward)));
        };
    };
    wf1_variant_assume_temp::<T>(spec, lift_action(next), lift_action(forward), lift_state(asm), lift_state(p), lift_state(q));
}

pub proof fn leads_to_confluence_self_temp<T>(spec: TempPred<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(p.and(not(q)).and(next).implies(later(p)))),
        spec.entails(p.leads_to(q)),
        spec.entails(always(next)),
    ensures
        spec.entails(p.leads_to(p.and(q))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(p.and(q)).satisfied_by(ex) by {
        entails_apply::<T>(ex, spec, p.leads_to(q));
        entails_apply::<T>(ex, spec, always(next));
        entails_apply::<T>(ex, spec, always(p.and(not(q)).and(next).implies(later(p))));
        assert(p.leads_to(q).satisfied_by(ex));
        assert(always(next).satisfied_by(ex));
        assert(always(p.and(not(q)).and(next).implies(later(p))).satisfied_by(ex));
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(p.and(q)).satisfied_by(ex.suffix(i)) by {
            leads_to_unfold::<T>(ex, p, q);
            let q_idx = eventually_choose_witness::<T>(ex.suffix(i), q);
            always_propagate_forwards::<T>(ex, next, i);
            always_propagate_forwards::<T>(ex, p.and(not(q)).and(next).implies(later(p)), i);
            confluence_at_some_point::<T>(ex.suffix(i), next, p, q, q_idx);
        };
    };
}

pub proof fn leads_to_confluence_self<T>(spec: TempPred<T>, next: ActionPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        forall |s, s_prime: T| p(s) && !q(s) && #[trigger] next(s, s_prime) ==> p(s_prime),
        spec.entails(lift_state(p).leads_to(lift_state(q))),
        spec.entails(always(lift_action(next))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(p).and(lift_state(q)))),
{
    leads_to_confluence_self_temp::<T>(spec, lift_action(next), lift_state(p), lift_state(q));
}

/// Leads to q and r if (1) p leads to q, (2) p leads to r, (3) ~r and next preserve q and (4) ~q and next preserve r
/// pre:
///     spec |= [](q /\ ~r /\ next => q')
///     spec |= [](r /\ ~q /\ next => r')
///     spec |= p ~> q
///     spec |= p ~> r
///     spec |= []next
/// post:
///     spec |= p ~> q /\ r
pub proof fn leads_to_confluence_temp<T>(spec: TempPred<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(always(q.and(not(r)).and(next).implies(later(q)))),
        spec.entails(always(r.and(not(q)).and(next).implies(later(r)))),
        spec.entails(p.leads_to(q)),
        spec.entails(p.leads_to(r)),
        spec.entails(always(next)),
    ensures
        spec.entails(p.leads_to(q.and(r))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(q.and(r)).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(q.and(r)).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, always(next));

            implies_apply::<T>(ex, spec, always(q.and(not(r)).and(next).implies(later(q))));
            implies_apply::<T>(ex, spec, always(r.and(not(q)).and(next).implies(later(r))));

            implies_apply::<T>(ex, spec, p.leads_to(q));
            leads_to_unfold::<T>(ex, p, q);
            implies_apply::<T>(ex.suffix(i), p, eventually(q));
            let q_idx = eventually_choose_witness::<T>(ex.suffix(i), q);

            implies_apply::<T>(ex, spec, p.leads_to(r));
            leads_to_unfold::<T>(ex, p, r);
            implies_apply::<T>(ex.suffix(i), p, eventually(r));
            let r_idx = eventually_choose_witness::<T>(ex.suffix(i), r);

            if r_idx <= q_idx {
                execution_equality::<T>(ex.suffix(i).suffix(q_idx), ex.suffix(i).suffix(r_idx).suffix((q_idx - r_idx) as nat));

                always_propagate_forwards::<T>(ex, next, i + r_idx);
                execution_equality::<T>(ex.suffix(i + r_idx), ex.suffix(i).suffix(r_idx));

                always_propagate_forwards::<T>(ex, r.and(not(q)).and(next).implies(later(r)), i + r_idx);
                execution_equality::<T>(ex.suffix(i + r_idx), ex.suffix(i).suffix(r_idx));

                confluence_at_some_point(ex.suffix(i).suffix(r_idx), next, r, q, (q_idx - r_idx) as nat);
                let idx = choose |idx| q.and(r).satisfied_by(#[trigger] ex.suffix(i).suffix(r_idx).suffix(idx));
                execution_equality::<T>(ex.suffix(i).suffix(r_idx + idx), ex.suffix(i).suffix(r_idx).suffix(idx));
                eventually_proved_by_witness::<T>(ex.suffix(i), q.and(r), r_idx + idx);
            } else {
                execution_equality::<T>(ex.suffix(i).suffix(r_idx), ex.suffix(i).suffix(q_idx).suffix((r_idx - q_idx) as nat));

                always_propagate_forwards::<T>(ex, next, i + q_idx);
                execution_equality::<T>(ex.suffix(i + q_idx), ex.suffix(i).suffix(q_idx));

                always_propagate_forwards::<T>(ex, q.and(not(r)).and(next).implies(later(q)), i + q_idx);
                execution_equality::<T>(ex.suffix(i + q_idx), ex.suffix(i).suffix(q_idx));

                confluence_at_some_point(ex.suffix(i).suffix(q_idx), next, q, r, (r_idx - q_idx) as nat);
                let idx = choose |idx| q.and(r).satisfied_by(#[trigger] ex.suffix(i).suffix(q_idx).suffix(idx));
                execution_equality::<T>(ex.suffix(i).suffix(q_idx + idx), ex.suffix(i).suffix(q_idx).suffix(idx));
                eventually_proved_by_witness::<T>(ex.suffix(i), q.and(r), q_idx + idx);
            }
        }
    }
}

/// StatePred version of leads_to_confluence_temp
pub proof fn leads_to_confluence<T>(spec: TempPred<T>, next: ActionPred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        forall |s, s_prime: T| q(s) && !r(s) && #[trigger] next(s, s_prime) ==> q(s_prime),
        forall |s, s_prime: T| r(s) && !q(s) && #[trigger] next(s, s_prime) ==> r(s_prime),
        spec.entails(lift_state(p).leads_to(lift_state(q))),
        spec.entails(lift_state(p).leads_to(lift_state(r))),
        spec.entails(always(lift_action(next))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q).and(lift_state(r)))),
{
    leads_to_confluence_temp::<T>(spec, lift_action(next), lift_state(p), lift_state(q), lift_state(r));
}

/// Leads to q and r2 if (1) p leads to q and r1, (2) r1 leads to r2 and (3) ~r2 and next preserve q
/// pre:
///     spec |= [](q /\ ~r2 /\ next => q')
///     spec |= p ~> q /\ r1
///     spec |= r1 ~> r2
///     spec |= []next
/// post:
///     spec |= p ~> q /\ r2
pub proof fn leads_to_partial_confluence_temp<T>(spec: TempPred<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r1: TempPred<T>, r2: TempPred<T>)
    requires
        spec.entails(always(q.and(not(r2)).and(next).implies(later(q)))),
        spec.entails(p.leads_to(q.and(r1))),
        spec.entails(r1.leads_to(r2)),
        spec.entails(always(next)),
    ensures
        spec.entails(p.leads_to(q.and(r2))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(q.and(r2)).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(q.and(r2)).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, always(next));

            implies_apply::<T>(ex, spec, always(q.and(not(r2)).and(next).implies(later(q))));

            implies_apply::<T>(ex, spec, p.leads_to(q.and(r1)));
            leads_to_unfold::<T>(ex, p, q.and(r1));
            implies_apply::<T>(ex.suffix(i), p, eventually(q.and(r1)));
            let q_and_r1_idx = eventually_choose_witness::<T>(ex.suffix(i), q.and(r1));

            execution_equality::<T>(ex.suffix(i).suffix(q_and_r1_idx), ex.suffix(i + q_and_r1_idx));

            implies_apply::<T>(ex, spec, r1.leads_to(r2));
            leads_to_unfold::<T>(ex, r1, r2);
            implies_apply::<T>(ex.suffix(i + q_and_r1_idx), r1, eventually(r2));
            let r2_idx = eventually_choose_witness::<T>(ex.suffix(i + q_and_r1_idx), r2);

            always_propagate_forwards::<T>(ex, next, i + q_and_r1_idx);
            execution_equality::<T>(ex.suffix(i + q_and_r1_idx), ex.suffix(i).suffix(q_and_r1_idx));

            always_propagate_forwards::<T>(ex, q.and(not(r2)).and(next).implies(later(q)), i + q_and_r1_idx);
            execution_equality::<T>(ex.suffix(i + q_and_r1_idx), ex.suffix(i).suffix(q_and_r1_idx));

            confluence_at_some_point(ex.suffix(i).suffix(q_and_r1_idx), next, q, r2, r2_idx);
            let idx = choose |idx| q.and(r2).satisfied_by(#[trigger] ex.suffix(i).suffix(q_and_r1_idx).suffix(idx));
            execution_equality::<T>(ex.suffix(i).suffix(q_and_r1_idx + idx), ex.suffix(i).suffix(q_and_r1_idx).suffix(idx));
            eventually_proved_by_witness::<T>(ex.suffix(i), q.and(r2), q_and_r1_idx + idx);
        }
    }
}

/// StatePred version of leads_to_partial_confluence_temp
pub proof fn leads_to_partial_confluence<T>(spec: TempPred<T>, next: ActionPred<T>, p: StatePred<T>, q: StatePred<T>, r1: StatePred<T>, r2: StatePred<T>)
    requires
        forall |s, s_prime: T| q(s) && !r2(s) && #[trigger] next(s, s_prime) ==> q(s_prime),
        spec.entails(lift_state(p).leads_to(lift_state(q).and(lift_state(r1)))),
        spec.entails(lift_state(r1).leads_to(lift_state(r2))),
        spec.entails(always(lift_action(next))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q).and(lift_state(r2)))),
{
    leads_to_partial_confluence_temp::<T>(spec, lift_action(next), lift_state(p), lift_state(q), lift_state(r1), lift_state(r2));
}

/// Connects two valid implies.
/// pre:
///     |= p => q
///     |= q => r
/// post:
///     |= p => r
pub proof fn valid_implies_trans<T>(p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        valid(p.implies(q)),
        valid(q.implies(r)),
    ensures
        valid(p.implies(r)),
{
    assert forall |ex| p.satisfied_by(ex) implies r.satisfied_by(ex) by {
        implies_apply::<T>(ex, p, q);
        implies_apply::<T>(ex, q, r);
    };
}

/// If p implies q for all executions, p will leads to q anyway.
/// pre:
///     |= p => q
/// post:
///     spec |= p ~> q
/// Note: there is no constraint on spec, it can be true_pred().
pub proof fn valid_implies_implies_leads_to<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        valid(p.implies(q)),
    ensures
        spec.entails(p.leads_to(q)),
{
    valid_p_implies_always_p(p.implies(q));
    implies_to_leads_to(spec, p, q);
}

/// Weaken entails by implies.
/// pre:
///     |= p => q
///     spec |= p
/// post:
///     spec |= q
pub proof fn entails_weaken_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        valid(p.implies(q)),
        spec.entails(p),
    ensures
        spec.entails(q)
{
    entails_trans::<T>(spec, p, q);
}

/// Auto version of entails_weaken.
pub proof fn entails_weaken_auto<T>(spec: TempPred<T>)
    ensures
        forall |p: TempPred<T>, q: TempPred<T>|
            valid(p.implies(q)) && #[trigger] spec.entails(p) ==> #[trigger] spec.entails(q)
{
    assert forall |p: TempPred<T>, q: TempPred<T>| valid(p.implies(q)) && #[trigger] spec.entails(p)
    implies #[trigger] spec.entails(q) by {
        entails_weaken_temp::<T>(spec, p, q);
    };
}

/// Implies is preserved by and.
/// pre:
///     spec|= [](p1 => p2)
///     spec|= [](q1 => q2)
/// post:
///     spec|= [](p1 /\ q1 => p2 /\ q2)
pub proof fn implies_preserved_by_and_temp<T>(spec: TempPred<T>, p1: TempPred<T>, p2: TempPred<T>, q1: TempPred<T>, q2: TempPred<T>)
    requires
        spec.entails(always(p1.implies(p2))),
        spec.entails(always(q1.implies(q2))),
    ensures
        spec.entails(always(p1.and(q1).implies(p2.and(q2)))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(p1.and(q1).implies(p2.and(q2))).satisfied_by(ex) by {
        assert forall |i| #[trigger] p1.and(q1).satisfied_by(ex.suffix(i)) implies p2.and(q2).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, always(p1.implies(p2)));
            implies_apply::<T>(ex, spec, always(q1.implies(q2)));
            implies_apply::<T>(ex.suffix(i), p1, p2);
            implies_apply::<T>(ex.suffix(i), q1, q2);
        };
    };
}

/// Sandwich always implies with p.
/// pre:
///     spec |= [](q1 => q2)
/// post:
///     spec |= [](p /\ q1 => p /\ q2)
pub proof fn sandwich_always_implies_temp<T>(spec: TempPred<T>, p: TempPred<T>, q1: TempPred<T>, q2: TempPred<T>)
    requires
        spec.entails(always(q1.implies(q2))),
    ensures
        spec.entails(always(p.and(q1).implies(p.and(q2)))),
{
    implies_preserved_by_and_temp::<T>(spec, p, p, q1, q2);
}

/// Introduce always to both sides of implies.
/// pre:
///     |= p => q
/// post:
///     |= []p => []q
pub proof fn implies_preserved_by_always_temp<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        valid(p.implies(q)),
    ensures
        valid(always(p).implies(always(q))),
{
    assert forall |ex| always(p).satisfied_by(ex) implies always(q).satisfied_by(ex) by {
        assert forall |i:nat| q.satisfied_by(#[trigger] ex.suffix(i)) by {
            always_unfold::<T>(ex, p);
            implies_apply::<T>(ex.suffix(i), p, q);
        };
    };
}

/// StatePred version of implies_preserved_by_always_temp.
pub proof fn implies_preserved_by_always<T>(p: StatePred<T>, q: StatePred<T>)
    requires
        valid(lift_state(p).implies(lift_state(q))),
    ensures
        valid(always(lift_state(p)).implies(always(lift_state(q)))),
{
    implies_preserved_by_always_temp::<T>(lift_state(p), lift_state(q));
}

/// Auto version of implies_preserved_by_always_temp.
pub proof fn implies_preserved_by_always_auto<T>()
    ensures
        forall |p: TempPred<T>, q: TempPred<T>|
        #![trigger always(p), always(q)]
        valid(p.implies(q)) ==> valid(always(p).implies(always(q))),
{
    assert forall |p: TempPred<T>, q: TempPred<T>| #[trigger] valid(p.implies(q))
    implies valid(always(p).implies(always(q))) by {
        implies_preserved_by_always_temp::<T>(p, q);
    };
}

/// Weaken always by implies.
/// pre:
///     |= p => q
///     spec |= []p
/// post:
///     spec |= []q
pub proof fn always_weaken_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        valid(p.implies(q)),
        spec.entails(always(p)),
    ensures
        spec.entails(always(q)),
{
    implies_preserved_by_always_temp::<T>(p, q);
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(q).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, always(p));
        implies_apply::<T>(ex, always(p), always(q));
    };
}

/// StatePred version of always_weaken_temp.
pub proof fn always_weaken<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        valid(lift_state(p).implies(lift_state(q))),
        spec.entails(always(lift_state(p))),
    ensures
        spec.entails(always(lift_state(q))),
{
    always_weaken_temp::<T>(spec, lift_state(p), lift_state(q));
}

/// Merge an always and an eventually into an eventually.
/// pre:
///     spec |= []p
///     spec |= <>q
/// post:
///     spec |= <>(p /\ q)
pub proof fn always_and_eventually_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(p)),
        spec.entails(eventually(q)),
    ensures
        spec.entails(eventually(p.and(q))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies eventually(p.and(q)).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, always(p));
        implies_apply::<T>(ex, spec, eventually(q));
        let witness_idx = eventually_choose_witness::<T>(ex, q);
        eventually_proved_by_witness::<T>(ex, p.and(q), witness_idx);
    };
}

/// StatePred version of always_and_eventually_temp.
pub proof fn always_and_eventually<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        spec.entails(always(lift_state(p))),
        spec.entails(eventually(lift_state(q))),
    ensures
        spec.entails(eventually(lift_state(p).and(lift_state(q)))),
{
    always_and_eventually_temp::<T>(spec, lift_state(p), lift_state(q));
}

/// Introduce leads_to when there is always.
/// pre:
///     spec |= []q
/// post:
///     spec |= p ~> []q
pub proof fn always_prepend_leads_to_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(q)),
    ensures
        spec.entails(p.leads_to(always(q))),
{
    assert forall |ex| spec.satisfied_by(ex) implies #[trigger] p.leads_to(always(q)).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, always(q));
        always_double::<T>(ex, q);
        assert forall |i| p.satisfied_by(#[trigger] ex.suffix(i)) implies eventually(always(q)).satisfied_by(ex.suffix(i)) by {
            always_propagate_forwards::<T>(ex, always(q), i);
            always_unfold::<T>(ex.suffix(i), always(q));
            eventually_proved_by_witness::<T>(ex.suffix(i), always(q), 0);
        };
    };
}

/// StatePred version of always_prepend_leads_to_temp.
pub proof fn always_prepend_leads_to<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        spec.entails(always(lift_state(q))),
    ensures
        spec.entails(lift_state(p).leads_to(always(lift_state(q)))),
{
    always_prepend_leads_to_temp::<T>(spec, lift_state(p), lift_state(q));
}

/// Introduce always to both sides of always implies.
/// pre:
///     spec |= [](p => q)
/// post:
///     spec |= []([]p => []q)
pub proof fn always_implies_preserved_by_always_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(p.implies(q))),
    ensures
        spec.entails(always(always(p).implies(always(q)))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(always(p).implies(always(q))).satisfied_by(ex) by {
        assert forall |i| #[trigger] always(p).satisfied_by(ex.suffix(i)) implies always(q).satisfied_by(ex.suffix(i)) by {
            assert forall |j| #[trigger] q.satisfied_by(ex.suffix(i).suffix(j)) by {
                implies_apply::<T>(ex, spec, always(p.implies(q)));
                always_unfold::<T>(ex, p.implies(q));
                execution_equality::<T>(ex.suffix(i + j), ex.suffix(i).suffix(j));

                always_unfold::<T>(ex.suffix(i), p);

                implies_apply::<T>(ex.suffix(i).suffix(j), p, q);
            };
        };
    };
}

/// StatePred version of always_implies_preserved_by_always_temp.
pub proof fn always_implies_preserved_by_always<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        spec.entails(always(lift_state(p).implies(lift_state(q)))),
    ensures
        spec.entails(always(always(lift_state(p)).implies(always(lift_state(q))))),
{
    always_implies_preserved_by_always_temp::<T>(spec, lift_state(p), lift_state(q));
}

/// Weaken always implies by implies.
/// pre:
///     spec |= [](p2 => p1)
///     spec |= [](q1 => q2)
///     spec |= [](p1 => q1)
/// post:
///     spec |= [](p2 => q2)
pub proof fn always_implies_weaken_temp<T>(spec: TempPred<T>, p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>)
    requires
        spec.entails(always(p2.implies(p1))),
        spec.entails(always(q1.implies(q2))),
        spec.entails(always(p1.implies(q1))),
    ensures
        spec.entails(always(p2.implies(q2))),
{
    always_implies_trans_temp::<T>(spec, p2, p1, q1);
    always_implies_trans_temp::<T>(spec, p2, q1, q2);
}

/// Auto version of always_implies_weaken_temp.
pub proof fn always_implies_weaken_auto<T>(spec: TempPred<T>)
    ensures
        forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
            spec.entails(always(p2.implies(p1))) && spec.entails(always(q1.implies(q2))) && spec.entails(#[trigger] always(p1.implies(q1)))
            ==> spec.entails(#[trigger] always(p2.implies(q2)))
{
    assert forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
    spec.entails(always(p2.implies(p1))) && spec.entails(always(q1.implies(q2))) && spec.entails(#[trigger] always(p1.implies(q1)))
    implies spec.entails(#[trigger] always(p2.implies(q2))) by {
        always_implies_weaken_temp(spec, p1, q1, p2, q2);
    };
}

/// Connect two implies inside always by transitivity.
/// pre:
///     spec |= [](p => q)
///     spec |= [](q => r)
/// post:
///     spec |= [](p => r)
pub proof fn always_implies_trans_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(always(p.implies(q))),
        spec.entails(always(q.implies(r))),
    ensures
        spec.entails(always(p.implies(r))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(p.implies(r)).satisfied_by(ex) by {
        assert forall |i: nat| #[trigger] p.satisfied_by(ex.suffix(i))
        implies r.satisfied_by(ex.suffix(i)) by {
            entails_apply(ex, spec, always(p.implies(q)));
            entails_apply(ex, spec, always(q.implies(r)));
            always_unfold(ex, p.implies(q));
            always_unfold(ex, q.implies(r));
        }
    };
}

/// StatePred version of always_implies_trans_temp.
pub proof fn always_implies_trans<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        spec.entails(always(lift_state(p).implies(lift_state(q)))),
        spec.entails(always(lift_state(q).implies(lift_state(r)))),
    ensures
        spec.entails(always(lift_state(p).implies(lift_state(r)))),
{
    always_implies_trans_temp::<T>(spec, lift_state(p), lift_state(q), lift_state(r));
}

/// Auto version of always_implies_trans_temp.
pub proof fn always_implies_trans_auto<T>(spec: TempPred<T>)
    ensures
        forall |p: TempPred<T>, q: TempPred<T>, r: TempPred<T>|
            #[trigger] spec.entails(always(p.implies(q))) && #[trigger] spec.entails(always(q.implies(r)))
            ==> spec.entails(always(p.implies(r)))
{
    assert forall |p: TempPred<T>, q: TempPred<T>, r: TempPred<T>|
    #[trigger] spec.entails(always(p.implies(q))) && #[trigger] spec.entails(always(q.implies(r)))
    implies spec.entails(always(p.implies(r))) by {
        always_implies_trans_temp(spec, p, q, r);
    };
}

/// Introduce eventually to both sides of implies.
/// pre:
///     |= p => q
/// post:
///     |= <>p => <>q
pub proof fn implies_preserved_by_eventually_temp<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        valid(p.implies(q)),
    ensures
        valid(eventually(p).implies(eventually(q))),
{
    assert forall |ex| eventually(p).satisfied_by(ex) implies eventually(q).satisfied_by(ex) by {
        eventually_unfold::<T>(ex, p);
        let p_witness = eventually_choose_witness::<T>(ex, p);
        implies_apply::<T>(ex.suffix(p_witness), p, q);
    };
}

pub proof fn partially_strengthen_spec<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.and(q).entails(r),
        valid(p.implies(q)),
    ensures
        spec.and(p).entails(r),
{
    assert(p.entails(q));
    entails_and_different_temp::<T>(spec, p, spec, q);
    entails_trans(spec.and(p), spec.and(q), r);
}

/// Weaken eventually by implies.
/// pre:
///     |= p => q
///     spec |= <>p
/// post:
///     spec |= <>q
pub proof fn eventually_weaken_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        valid(p.implies(q)),
        spec.entails(eventually(p)),
    ensures
        spec.entails(eventually(q)),
{
    implies_preserved_by_eventually_temp::<T>(p, q);
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies eventually(q).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, eventually(p));
        implies_apply::<T>(ex, eventually(p), eventually(q));
    };
}

/// StatePred version of eventually_weaken_temp.
pub proof fn eventually_weaken<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        valid(lift_state(p).implies(lift_state(q))),
        spec.entails(eventually(lift_state(p))),
    ensures
        spec.entails(eventually(lift_state(q))),
{
    eventually_weaken_temp::<T>(spec, lift_state(p), lift_state(q));
}

/// Auto version of eventually_weaken_temp.
pub proof fn eventually_weaken_auto<T>(spec: TempPred<T>)
    ensures
        forall |p: TempPred<T>, q: TempPred<T>|
            valid(p.implies(q)) && spec.entails(#[trigger] eventually(p))
            ==> spec.entails(#[trigger] eventually(q)),
{
    assert forall |p: TempPred<T>, q: TempPred<T>|
    valid(p.implies(q)) && spec.entails(#[trigger] eventually(p))
    implies spec.entails(#[trigger] eventually(q)) by {
        eventually_weaken_temp(spec, p, q);
    };
}

/// Get eventually from leads_to.
/// pre:
///     spec |= p
///     spec |= p ~> q
/// post:
///     spec |= <>q
pub proof fn leads_to_apply_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(p),
        spec.entails(p.leads_to(q)),
    ensures
        spec.entails(eventually(q)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies eventually(q).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, p);
        implies_apply::<T>(ex, spec, p.leads_to(q));
        leads_to_unfold::<T>(ex, p, q);
        execution_equality::<T>(ex, ex.suffix(0));
        implies_apply::<T>(ex, p, eventually(q));
    };
}

/// StatePred version of leads_to_apply_temp
pub proof fn leads_to_apply<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        spec.entails(lift_state(p)),
        spec.entails(lift_state(p).leads_to(lift_state(q))),
    ensures
        spec.entails(eventually(lift_state(q))),
{
    leads_to_apply_temp::<T>(spec, lift_state(p), lift_state(q));
}

/// Connect two leads_to by transitivity.
/// pre:
///     spec |= p ~> q
///     spec |= q ~> r
/// post:
///     spec |= p ~> r
pub proof fn leads_to_trans_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.leads_to(q)),
        spec.entails(q.leads_to(r)),
    ensures
        spec.entails(p.leads_to(r)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies p.leads_to(r).satisfied_by(ex) by {
        assert forall |i: nat| #[trigger] p.satisfied_by(ex.suffix(i))
        implies eventually(r).satisfied_by(ex.suffix(i)) by {
            entails_apply(ex, spec, p.leads_to(q));
            always_unfold(ex, p.implies(eventually(q)));
            implies_apply(ex.suffix(i), p, eventually(q));
            eventually_unfold(ex.suffix(i), q);
            let q_witness_idx = eventually_choose_witness(ex.suffix(i), q);
            execution_equality::<T>(ex.suffix(i + q_witness_idx), ex.suffix(i).suffix(q_witness_idx));

            entails_apply(ex, spec, q.leads_to(r));
            always_unfold(ex, q.implies(eventually(r)));
            implies_apply(ex.suffix(i + q_witness_idx), q, eventually(r));
            execution_equality::<T>(ex.suffix(i + q_witness_idx), ex.suffix(i).suffix(q_witness_idx));

            eventually_propagate_backwards(ex.suffix(i), r, q_witness_idx);
        }
    };
}

/// StatePred version of leads_to_trans_temp.
pub proof fn leads_to_trans<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        spec.entails(lift_state(p).leads_to(lift_state(q))),
        spec.entails(lift_state(q).leads_to(lift_state(r))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(r))),
{
    leads_to_trans_temp::<T>(spec, lift_state(p), lift_state(q), lift_state(r));
}

/// Auto version of leads_to_trans_temp.
pub proof fn leads_to_trans_auto<T>(spec: TempPred<T>)
    ensures
        forall |p: TempPred<T>, q: TempPred<T>, r: TempPred<T>|
            #[trigger] spec.entails(p.leads_to(q)) && #[trigger] spec.entails(q.leads_to(r))
            ==> spec.entails(p.leads_to(r))
{
    assert forall |p: TempPred<T>, q: TempPred<T>, r: TempPred<T>|
    #[trigger] spec.entails(p.leads_to(q)) && #[trigger] spec.entails(q.leads_to(r))
    implies spec.entails(p.leads_to(r)) by {
        leads_to_trans_temp(spec, p, q, r);
    };
}

/// Relaxed version of leads_to_trans_temp.
/// pre:
///     |= q1 => q2
///     spec |= p ~> q1
///     spec |= q2 ~> r
/// post:
///     spec |= p ~> r
pub proof fn leads_to_trans_relaxed_temp<T>(spec: TempPred<T>, p: TempPred<T>, q1: TempPred<T>, q2: TempPred<T>, r: TempPred<T>)
    requires
        valid(q1.implies(q2)),
        spec.entails(p.leads_to(q1)),
        spec.entails(q2.leads_to(r)),
    ensures
        spec.entails(p.leads_to(r)),
{
    implies_to_leads_to::<T>(spec, q1, q2);
    leads_to_trans_temp::<T>(spec, p, q1, q2);
    leads_to_trans_temp::<T>(spec, p, q2, r);
}

/// Auto version of leads_to_trans_relaxed_temp.
/// This one is heavy, but saves a lot of tedious steps.
pub proof fn leads_to_trans_relaxed_auto<T>(spec: TempPred<T>)
    ensures
        forall |p: TempPred<T>, q1: TempPred<T>, q2: TempPred<T>, r: TempPred<T>|
        valid(q1.implies(q2)) && #[trigger] spec.entails(p.leads_to(q1)) && #[trigger] spec.entails(q2.leads_to(r))
        ==> spec.entails(p.leads_to(r)),
{
    assert forall |p: TempPred<T>, q1: TempPred<T>, q2: TempPred<T>, r: TempPred<T>|
    valid(q1.implies(q2)) && #[trigger] spec.entails(p.leads_to(q1)) && #[trigger] spec.entails(q2.leads_to(r))
    implies spec.entails(p.leads_to(r)) by {
        leads_to_trans_relaxed_temp::<T>(spec, p, q1, q2, r);
    };
}

/// Weaken leads_to by implies.
/// pre:
///     spec |= [](p2 => p1)
///     spec |= [](q1 => q2)
///     spec |= p1 ~> q1
/// post:
///     spec |= p2 ~> q2
pub proof fn leads_to_weaken_temp<T>(spec: TempPred<T>, p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>)
    requires
        spec.entails(always(p2.implies(p1))),
        spec.entails(always(q1.implies(q2))),
        spec.entails(p1.leads_to(q1)),
    ensures
        spec.entails(p2.leads_to(q2)),
{
    implies_to_leads_to::<T>(spec, p2, p1);
    implies_to_leads_to::<T>(spec, q1, q2);
    leads_to_trans_temp::<T>(spec, p2, p1, q1);
    leads_to_trans_temp::<T>(spec, p2, q1, q2);
}

/// Auto version of leads_to_weaken_temp.
pub proof fn leads_to_weaken_auto<T>(spec: TempPred<T>)
    ensures
        forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
            spec.entails(always(p2.implies(p1))) && spec.entails(always(q1.implies(q2))) && spec.entails(#[trigger] p1.leads_to(q1))
            ==> spec.entails(#[trigger] p2.leads_to(q2))
{
    assert forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
    spec.entails(always(p2.implies(p1))) && spec.entails(always(q1.implies(q2))) && spec.entails(#[trigger] p1.leads_to(q1))
    implies spec.entails(#[trigger] p2.leads_to(q2)) by {
        leads_to_weaken_temp(spec, p1, q1, p2, q2);
    };
}

/// Combine the premises of two leads_to using or.
/// pre:
///     spec |= p ~> r
///     spec |= q ~> r
/// post:
///     spec |= (p \/ q) ~> r
pub proof fn or_leads_to_combine_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.leads_to(r)),
        spec.entails(q.leads_to(r)),
    ensures
        spec.entails(p.or(q).leads_to(r)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.or(q).leads_to(r).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.or(q).satisfied_by(ex.suffix(i)) implies eventually(r).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, p.leads_to(r));
            implies_apply::<T>(ex, spec, q.leads_to(r));
            leads_to_unfold::<T>(ex, p, r);
            leads_to_unfold::<T>(ex, q, r);
        };
    };
}

/// StatePred version of or_leads_to_combine_temp.
pub proof fn or_leads_to_combine<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        spec.entails(lift_state(p).leads_to(lift_state(r))),
        spec.entails(lift_state(q).leads_to(lift_state(r))),
    ensures
        spec.entails(lift_state(p).or(lift_state(q)).leads_to(lift_state(r))),
{
    or_leads_to_combine_temp::<T>(spec, lift_state(p), lift_state(q), lift_state(r));
}

/// Specialized version of or_leads_to_combine used for eliminating q in premise.
/// pre:
///     spec |= p /\ r ~> q
///     spec |= p /\ ~r ~> q
/// post:
///     spec |= p ~> q
pub proof fn leads_to_combine_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.and(r).leads_to(q)),
        spec.entails(p.and(not(r)).leads_to(q)),
    ensures
        spec.entails(p.leads_to(q)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(q).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(q).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, p.and(r).leads_to(q));
            implies_apply::<T>(ex, spec, p.and(not(r)).leads_to(q));
            if r.satisfied_by(ex.suffix(i)) {
                implies_apply::<T>(ex.suffix(i), p.and(r), eventually(q));
            } else {
                implies_apply::<T>(ex.suffix(i), p.and(not(r)), eventually(q));
            }
        };
    };
}

/// StatePred version of leads_to_combine_temp.
pub proof fn leads_to_combine<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        spec.entails(lift_state(p).and(lift_state(r)).leads_to(lift_state(q))),
        spec.entails(lift_state(p).and(not(lift_state(r))).leads_to(lift_state(q))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q))),
{
    leads_to_combine_temp::<T>(spec, lift_state(p), lift_state(q), lift_state(r));
}

/// Remove r from the premise of leads_to if always r.
/// pre:
///     spec |= []r
///     spec |= (p /\ r) ~> q
/// post:
///     spec |= p ~> q
pub proof fn leads_to_assume_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(always(r)),
        spec.entails(p.and(r).leads_to(q)),
    ensures
        spec.entails(p.leads_to(q)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(q).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(q).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, always(r));
            implies_apply::<T>(ex, spec, p.and(r).leads_to(q));
            implies_apply::<T>(ex.suffix(i), p.and(r), eventually(q));
        };
    };
}

/// StatePred version of leads_to_assume_temp.
pub proof fn leads_to_assume<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        spec.entails(always(lift_state(r))),
        spec.entails(lift_state(p).and(lift_state(r)).leads_to(lift_state(q))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q))),
{
    leads_to_assume_temp::<T>(spec, lift_state(p), lift_state(q), lift_state(r));
}

/// Remove ~q from the premise of leads_to if q is the conclusion.
/// pre:
///     spec |= (p /\ ~q) ~> q
/// post:
///     spec |= p ~> q
pub proof fn leads_to_assume_not_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(p.and(not(q)).leads_to(q)),
    ensures
        spec.entails(p.leads_to(q)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(q).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(q).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, p.and(not(q)).leads_to(q));
            if not(q).satisfied_by(ex.suffix(i)) {
                implies_apply::<T>(ex.suffix(i), p.and(not(q)), eventually(q));
            } else {
                execution_equality::<T>(ex.suffix(i), ex.suffix(i).suffix(0));
            }
        };
    };
}

/// StatePred version of leads_to_assume_not_temp.
pub proof fn leads_to_assume_not<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        spec.entails(lift_state(p).and(not(lift_state(q))).leads_to(lift_state(q))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q))),
{
    leads_to_assume_not_temp::<T>(spec, lift_state(p), lift_state(q));
}

/// Combine the conclusions of two leads_to if the conclusions are stable.
/// pre:
///     spec |= p ~> []q
///     spec |= p ~> []r
/// post:
///     spec |= p ~> [](q /\ r)
pub proof fn leads_to_always_combine_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.leads_to(always(q))),
        spec.entails(p.leads_to(always(r))),
    ensures
        spec.entails(p.leads_to(always(q.and(r)))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(always(q.and(r))).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(always(q.and(r))).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, p.leads_to(always(q)));
            implies_apply::<T>(ex, spec, p.leads_to(always(r)));

            implies_apply::<T>(ex.suffix(i), p, eventually(always(q)));
            implies_apply::<T>(ex.suffix(i), p, eventually(always(r)));

            let witness_q_idx = eventually_choose_witness::<T>(ex.suffix(i), always(q));
            let witness_r_idx = eventually_choose_witness::<T>(ex.suffix(i), always(r));

            if witness_q_idx < witness_r_idx {
                always_propagate_forwards::<T>(ex.suffix(i).suffix(witness_q_idx), q, (witness_r_idx - witness_q_idx) as nat);
                execution_equality::<T>(ex.suffix(i).suffix(witness_r_idx), ex.suffix(i).suffix(witness_q_idx).suffix((witness_r_idx - witness_q_idx) as nat));
                eventually_proved_by_witness(ex.suffix(i), always(q.and(r)), witness_r_idx);
            } else {
                always_propagate_forwards::<T>(ex.suffix(i).suffix(witness_r_idx), r, (witness_q_idx - witness_r_idx) as nat);
                execution_equality::<T>(ex.suffix(i).suffix(witness_q_idx), ex.suffix(i).suffix(witness_r_idx).suffix((witness_q_idx - witness_r_idx) as nat));
                eventually_proved_by_witness(ex.suffix(i), always(q.and(r)), witness_q_idx);
            }
        };
    };
}

/// StatePred version of leads_to_always_combine_temp.
pub proof fn leads_to_always_combine<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        spec.entails(lift_state(p).leads_to(always(lift_state(q)))),
        spec.entails(lift_state(p).leads_to(always(lift_state(r)))),
    ensures
        spec.entails(lift_state(p).leads_to(always(lift_state(q).and(lift_state(r))))),
{
    leads_to_always_combine_temp::<T>(spec, lift_state(p), lift_state(q), lift_state(r));
}

/// Weaken version of leads_to_always_combine by dropping the always in both conclusions.
/// pre:
///     spec |= p ~> []q
///     spec |= p ~> []r
/// post:
///     spec |= p ~> (q /\ r)
pub proof fn leads_to_always_combine_weaken_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.leads_to(always(q))),
        spec.entails(p.leads_to(always(r))),
    ensures
        spec.entails(p.leads_to(q.and(r))),
{
    leads_to_always_combine_temp::<T>(spec, p, q, r);
    always_implies_current::<T>(q.and(r));
    leads_to_weaken_temp::<T>(spec, p, always(q.and(r)), p, q.and(r));
}

/// StatePred version of leads_to_always_combine_weaken_temp.
pub proof fn leads_to_always_combine_weaken<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        spec.entails(lift_state(p).leads_to(always(lift_state(q)))),
        spec.entails(lift_state(p).leads_to(always(lift_state(r)))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q).and(lift_state(r)))),
{
    leads_to_always_combine_weaken_temp::<T>(spec, lift_state(p), lift_state(q), lift_state(r));
}

/// Weaken version of leads_to_always_combine by dropping the always in only one conclusion.
/// pre:
///     spec |= p ~> []q
///     spec |= p ~> []r
/// post:
///     spec |= p ~> (q /\ []r)
pub proof fn leads_to_always_combine_partially_weaken_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.leads_to(always(q))),
        spec.entails(p.leads_to(always(r))),
    ensures
        spec.entails(p.leads_to(q.and(always(r)))),
{

    leads_to_always_combine_temp::<T>(spec, p, q, r);
    always_distributed_by_and::<T>(q, r);
    leads_to_weaken_temp::<T>(spec, p, always(q.and(r)), p, always(q).and(always(r)));
    always_implies_current::<T>(q);
    implies_preserved_by_and_temp::<T>(spec, always(q), q, always(r), always(r));
    leads_to_weaken_temp::<T>(spec, p, always(q).and(always(r)), p, q.and(always(r)));
}

/// StatePred version of leads_to_always_combine_partially_weaken_temp.
pub proof fn leads_to_always_combine_partially_weaken<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        spec.entails(lift_state(p).leads_to(always(lift_state(q)))),
        spec.entails(lift_state(p).leads_to(always(lift_state(r)))),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q).and(always(lift_state(r))))),
{
    leads_to_always_combine_partially_weaken_temp::<T>(spec, lift_state(p), lift_state(q), lift_state(r));
}

/// Get leads_to always.
/// pre:
///     spec |= [](q /\ next => q')
///     spec |= []next
///     spec |= p ~> q
/// post:
///     spec |= p ~> []q
pub proof fn leads_to_stable_temp<T>(spec: TempPred<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(q.and(next).implies(later(q)))),
        spec.entails(always(next)),
        spec.entails(p.leads_to(q)),
    ensures
        spec.entails(p.leads_to(always(q))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(always(q)).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(always(q)).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, p.leads_to(q));
            leads_to_unfold::<T>(ex, p, q);
            implies_apply::<T>(ex.suffix(i), p, eventually(q));
            let witness_idx = eventually_choose_witness::<T>(ex.suffix(i), q);

            implies_apply::<T>(ex, spec, always(q.and(next).implies(later(q))));
            always_propagate_forwards::<T>(ex, q.and(next).implies(later(q)), i);
            always_propagate_forwards::<T>(ex.suffix(i), q.and(next).implies(later(q)), witness_idx);

            implies_apply::<T>(ex, spec, always(next));
            always_propagate_forwards::<T>(ex, next, i);
            always_propagate_forwards::<T>(ex.suffix(i), next, witness_idx);

            assert forall |j| #[trigger] q.satisfied_by(ex.suffix(i).suffix(witness_idx).suffix(j)) by {
                assert forall |idx| q.satisfied_by(#[trigger] ex.suffix(i).suffix(witness_idx).suffix(idx))
                && next.satisfied_by(ex.suffix(i).suffix(witness_idx).suffix(idx))
                implies q.satisfied_by(ex.suffix(i).suffix(witness_idx).suffix(idx + 1)) by {
                    implies_apply::<T>(ex.suffix(i).suffix(witness_idx).suffix(idx), q.and(next), later(q));
                    execution_equality::<T>(ex.suffix(i).suffix(witness_idx).suffix(idx + 1), ex.suffix(i).suffix(witness_idx).suffix(idx).suffix(1));
                };
                next_preserves_inv_rec::<T>(ex.suffix(i).suffix(witness_idx), next, q, j);
            };

            eventually_proved_by_witness::<T>(ex.suffix(i), always(q), witness_idx);
        };
    };
}

/// Get leads_to always by assuming always asm.
/// pre:
///     spec |= [](q /\ next /\ asm => q')
///     spec |= []next
///     spec |= p ~> q
/// post:
///     spec |= p /\ []asm ~> []q
pub proof fn leads_to_stable_assume_temp<T>(spec: TempPred<T>, next: TempPred<T>, asm: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(q.and(next).and(asm).implies(later(q)))),
        spec.entails(always(next)),
        spec.entails(p.leads_to(q)),
    ensures
        spec.entails(p.and(always(asm)).leads_to(always(q))),
{
    let p_and_always_asm = p.and(always(asm));
    let q_and_always_asm = q.and(always(asm));

    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(q_and_always_asm.and(next).implies(later(q_and_always_asm))).satisfied_by(ex) by {
        assert forall |i| #[trigger] q_and_always_asm.and(next).satisfied_by(ex.suffix(i))
        implies later(q_and_always_asm).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, always(q.and(next).and(asm).implies(later(q))));
            always_to_current::<T>(ex.suffix(i), asm);
            implies_apply::<T>(ex.suffix(i), q.and(next).and(asm), later(q));
            always_propagate_forwards::<T>(ex.suffix(i), asm, 1);
        };
    };

    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies p_and_always_asm.leads_to(q_and_always_asm).satisfied_by(ex) by {
        assert forall |i| #[trigger] p_and_always_asm.satisfied_by(ex.suffix(i))
        implies eventually(q_and_always_asm).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, p.leads_to(q));
            leads_to_unfold::<T>(ex, p, q);
            implies_apply::<T>(ex.suffix(i), p, eventually(q));
            let witness_idx = eventually_choose_witness::<T>(ex.suffix(i), q);
            always_propagate_forwards::<T>(ex.suffix(i), asm, witness_idx);
            eventually_proved_by_witness::<T>(ex.suffix(i), q_and_always_asm, witness_idx);
        };
    };

    leads_to_stable_temp::<T>(spec, next, p_and_always_asm, q_and_always_asm);

    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies p.and(always(asm)).leads_to(always(q)).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.and(always(asm)).satisfied_by(ex.suffix(i))
        implies eventually(always(q)).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, p_and_always_asm.leads_to(always(q_and_always_asm)));
            leads_to_unfold::<T>(ex, p_and_always_asm, always(q_and_always_asm));

            implies_apply::<T>(ex.suffix(i), p_and_always_asm, eventually(always(q_and_always_asm)));
            let witness_idx = eventually_choose_witness::<T>(ex.suffix(i), always(q_and_always_asm));
            always_unfold::<T>(ex.suffix(i).suffix(witness_idx), q_and_always_asm);
            eventually_proved_by_witness::<T>(ex.suffix(i), always(q), witness_idx);
        };
    };
}

/// StatePred version of leads_to_stable_temp.
pub proof fn leads_to_stable<T>(spec: TempPred<T>, next: ActionPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        forall |s, s_prime: T| q(s) && #[trigger] next(s, s_prime) ==> q(s_prime),
        spec.entails(always(lift_action(next))),
        spec.entails(lift_state(p).leads_to(lift_state(q))),
    ensures
        spec.entails(lift_state(p).leads_to(always(lift_state(q)))),
{
    leads_to_stable_temp::<T>(spec, lift_action(next), lift_state(p), lift_state(q));
}

/// StatePred version of leads_to_stable_assume_temp.
pub proof fn leads_to_stable_assume<T>(spec: TempPred<T>, next: ActionPred<T>, asm: StatePred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        forall |s, s_prime: T| q(s) && #[trigger] next(s, s_prime) && asm(s) ==> q(s_prime),
        spec.entails(always(lift_action(next))),
        spec.entails(lift_state(p).leads_to(lift_state(q))),
    ensures
        spec.entails(lift_state(p).and(always(lift_state(asm))).leads_to(always(lift_state(q)))),
{
    leads_to_stable_assume_temp::<T>(spec, lift_action(next), lift_state(asm), lift_state(p), lift_state(q));
}

/// Get leads_to always by assuming always p.
/// pre:
///     |= q /\ next /\ asm => q'
///     spec |= []next
///     spec |= []([]p => []asm)
///     spec |= p ~> q
/// post:
///     spec |= []p ~> []q
pub proof fn leads_to_stable_assume_p<T>(spec: TempPred<T>, next: ActionPred<T>, asm: StatePred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        forall |s, s_prime: T| q(s) && #[trigger] next(s, s_prime) && asm(s) ==> q(s_prime),
        spec.entails(always(lift_action(next))),
        spec.entails(always(always(lift_state(p)).implies(always(lift_state(asm))))),
        spec.entails(lift_state(p).leads_to(lift_state(q))),
    ensures
        spec.entails(always(lift_state(p)).leads_to(always(lift_state(q)))),
{
    leads_to_stable_assume::<T>(spec, next, asm, p, q);

    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(lift_state(p)).leads_to(always(lift_state(q))).satisfied_by(ex) by {
        assert forall |i| #[trigger] always(lift_state(p)).satisfied_by(ex.suffix(i)) implies eventually(always(lift_state(q))).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, always(always(lift_state(p)).implies(always(lift_state(asm)))));
            implies_apply::<T>(ex.suffix(i), always(lift_state(p)), always(lift_state(asm)));

            always_to_current::<T>(ex.suffix(i), lift_state(p));

            implies_apply::<T>(ex, spec, lift_state(p).and(always(lift_state(asm))).leads_to(always(lift_state(q))));
            implies_apply::<T>(ex.suffix(i), lift_state(p).and(always(lift_state(asm))), eventually(always(lift_state(q))));
        };
    };
}

/// Combination of leads_to_stable_assume_p and leads_to_always_combine_temp.
pub proof fn leads_to_stable_assume_p_combine<T>(spec: TempPred<T>, next: ActionPred<T>, asm: StatePred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        forall |s, s_prime: T| q(s) && #[trigger] next(s, s_prime) && asm(s) ==> q(s_prime),
        forall |s, s_prime: T| r(s) && #[trigger] next(s, s_prime) && asm(s) ==> r(s_prime),
        spec.entails(always(lift_action(next))),
        spec.entails(always(always(lift_state(p)).implies(always(lift_state(asm))))),
        spec.entails(lift_state(p).leads_to(lift_state(q))),
        spec.entails(lift_state(p).leads_to(lift_state(r))),
    ensures
        spec.entails(always(lift_state(p)).leads_to(always(lift_state(q).and(lift_state(r))))),
{
    leads_to_stable_assume_p::<T>(spec, next, asm, p, q);
    leads_to_stable_assume_p::<T>(spec, next, asm, p, r);
    leads_to_always_combine_temp::<T>(spec, always(lift_state(p)), lift_state(q), lift_state(r));
}

/// Combination of leads_to_stable and leads_to_always_combine.
pub proof fn leads_to_stable_combine<T>(spec: TempPred<T>, next: ActionPred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        forall |s, s_prime: T| q(s) && #[trigger] next(s, s_prime) ==> q(s_prime),
        forall |s, s_prime: T| r(s) && #[trigger] next(s, s_prime) ==> r(s_prime),
        spec.entails(always(lift_action(next))),
        spec.entails(lift_state(p).leads_to(lift_state(q))),
        spec.entails(lift_state(p).leads_to(lift_state(r))),
    ensures
        spec.entails(lift_state(p).leads_to(always(lift_state(q).and(lift_state(r))))),
{
    leads_to_stable::<T>(spec, next, p, q);
    leads_to_stable::<T>(spec, next, p, r);
    leads_to_always_combine::<T>(spec, p, q, r);
}

/// Show that if the conclusion of leads_to is never true, then the premise of leads_to is never true
/// pre:
///     spec |= p ~> q
/// ensures:
///     spec |= []([]~q => []~p)
pub proof fn leads_to_contraposition_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(p.leads_to(q)),
    ensures
        spec.entails(always(always(not(q)).implies(always(not(p))))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(always(not(q)).implies(always(not(p)))).satisfied_by(ex) by {
        assert forall |i| #[trigger] always(not(q)).satisfied_by(ex.suffix(i)) implies always(not(p)).satisfied_by(ex.suffix(i)) by {
            assert forall |j| #[trigger] not(p).satisfied_by(ex.suffix(i).suffix(j)) by {
                implies_apply::<T>(ex, spec, p.leads_to(q));
                leads_to_unfold::<T>(ex, p, q);
                execution_equality::<T>(ex.suffix(i + j), ex.suffix(i).suffix(j));

                always_propagate_forwards::<T>(ex.suffix(i), not(q), j);
                not_eventually_by_always_not::<T>(ex.suffix(i).suffix(j), q);

                not_proved_by_contraposition::<T>(ex.suffix(i).suffix(j), p, eventually(q));
            };
        };
    };
}

/// StatePred version of leads_to_contraposition_temp
pub proof fn leads_to_contraposition<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        spec.entails(lift_state(p).leads_to(lift_state(q))),
    ensures
        spec.entails(always(always(not(lift_state(q))).implies(always(not(lift_state(p)))))),
{
    leads_to_contraposition_temp::<T>(spec, lift_state(p), lift_state(q));
}

}
