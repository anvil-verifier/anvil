// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::temporal_logic::defs::*;
use vstd::map_lib::*;
use vstd::prelude::*;

verus! {

proof fn later_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires later(p).satisfied_by(ex),
    ensures p.satisfied_by(ex.suffix(1)),
{}

proof fn always_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires always(p).satisfied_by(ex),
    ensures forall |i: nat| p.satisfied_by(#[trigger] ex.suffix(i)),
{}

proof fn eventually_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires eventually(p).satisfied_by(ex),
    ensures exists |i: nat| p.satisfied_by(#[trigger] ex.suffix(i)),
{}

proof fn not_eventually_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires not(eventually(p)).satisfied_by(ex),
    ensures forall |i| !p.satisfied_by(#[trigger] ex.suffix(i))
{}

proof fn stable_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires stable(p).satisfied_by(ex),
    ensures p.satisfied_by(ex) ==> forall |i| p.satisfied_by(#[trigger] ex.suffix(i)),
{}

proof fn leads_to_unfold<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires p.leads_to(q).satisfied_by(ex),
    ensures forall |i: nat| p.implies(eventually(q)).satisfied_by(#[trigger] ex.suffix(i)),
{
    always_unfold::<T>(ex, p.implies(eventually(q)));
}

proof fn weak_fairness_unfold<T>(ex: Execution<T>, p: ActionPred<T>)
    requires weak_fairness(p).satisfied_by(ex),
    ensures forall |i| always(lift_state(enabled(p))).implies(eventually(lift_action(p))).satisfied_by(#[trigger] ex.suffix(i)),
{
    leads_to_unfold::<T>(ex, always(lift_state(enabled(p))), lift_action(p));
}

proof fn always_lift_state_unfold<T>(ex: Execution<T>, p: StatePred<T>)
    requires always(lift_state(p)).satisfied_by(ex),
    ensures forall |i| p(#[trigger] ex.suffix(i).head()),
{
    always_unfold::<T>(ex, lift_state(p));
}

proof fn always_lift_action_unfold<T>(ex: Execution<T>, p: ActionPred<T>)
    requires always(lift_action(p)).satisfied_by(ex),
    ensures forall |i| p(#[trigger] ex.suffix(i).head(), ex.suffix(i).head_next()),
{
    always_unfold::<T>(ex, lift_action(p));
}

proof fn tla_forall_unfold<T, A>(ex: Execution<T>, a_to_p: spec_fn(A) -> TempPred<T>)
    requires tla_forall(a_to_p).satisfied_by(ex),
    ensures forall |a| #[trigger] a_to_p(a).satisfied_by(ex),
{}

proof fn tla_exists_unfold<T, A>(ex: Execution<T>, a_to_p: spec_fn(A) -> TempPred<T>)
    requires tla_exists(a_to_p).satisfied_by(ex),
    ensures exists |a| #[trigger] a_to_p(a).satisfied_by(ex),
{}

proof fn tla_exists_proved_by_witness<T, A>(ex: Execution<T>, a_to_p: spec_fn(A) -> TempPred<T>, witness_a: A)
    requires a_to_p(witness_a).satisfied_by(ex),
    ensures tla_exists(a_to_p).satisfied_by(ex)
{}

spec fn tla_exists_choose_witness<T, A>(ex: Execution<T>, a_to_p: spec_fn(A) -> TempPred<T>) -> A
    recommends exists |a| #[trigger] a_to_p(a).satisfied_by(ex),
{
    let witness = choose |a| #[trigger] a_to_p(a).satisfied_by(ex);
    witness
}

proof fn implies_apply<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.implies(q).satisfied_by(ex),
        p.satisfied_by(ex),
    ensures q.satisfied_by(ex),
{}

proof fn implies_contraposition_apply<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.implies(q).satisfied_by(ex),
        not(q).satisfied_by(ex),
    ensures not(p).satisfied_by(ex),
{}

proof fn implies_apply_with_always<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        always(p.implies(q)).satisfied_by(ex),
        always(p).satisfied_by(ex),
    ensures always(q).satisfied_by(ex),
{
    always_unfold::<T>(ex, p.implies(q));
    always_unfold::<T>(ex, p);
}

proof fn entails_apply<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.entails(q),
        p.satisfied_by(ex),
    ensures q.satisfied_by(ex),
{
    implies_apply::<T>(ex, p, q);
}

proof fn not_proved_by_contraposition<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.implies(q).satisfied_by(ex),
        not(q).satisfied_by(ex),
    ensures not(p).satisfied_by(ex)
{}

proof fn not_eventually_by_always_not<T>(ex: Execution<T>, p: TempPred<T>)
    requires always(not(p)).satisfied_by(ex),
    ensures not(eventually(p)).satisfied_by(ex),
{
    always_unfold::<T>(ex, not(p));
}

proof fn always_propagate_forwards<T>(ex: Execution<T>, p: TempPred<T>, i: nat)
    requires always(p).satisfied_by(ex),
    ensures always(p).satisfied_by(ex.suffix(i)),
{
    always_unfold::<T>(ex, p);
    assert forall |j| p.satisfied_by(#[trigger] ex.suffix(i).suffix(j)) by {
        execution_equality::<T>(ex.suffix(i + j), ex.suffix(i).suffix(j));
    };
}

proof fn always_double<T>(ex: Execution<T>, p: TempPred<T>)
    requires always(p).satisfied_by(ex),
    ensures always(always(p)).satisfied_by(ex),
{
    always_unfold::<T>(ex, p);
    assert forall |i| always(p).satisfied_by(#[trigger] ex.suffix(i)) by {
        always_propagate_forwards::<T>(ex, p, i);
    };
}

proof fn always_to_current<T>(ex: Execution<T>, p: TempPred<T>)
    requires always(p).satisfied_by(ex),
    ensures p.satisfied_by(ex),
{
    execution_equality::<T>(ex, ex.suffix(0));
}

proof fn always_to_future<T>(ex: Execution<T>, p: TempPred<T>, i: nat)
    requires always(p).satisfied_by(ex),
    ensures p.satisfied_by(ex.suffix(i))
{
    always_propagate_forwards::<T>(ex, p, i);
    always_to_current::<T>(ex.suffix(i), p);
}

proof fn eventually_propagate_backwards<T>(ex: Execution<T>, p: TempPred<T>, i: nat)
    requires eventually(p).satisfied_by(ex.suffix(i)),
    ensures eventually(p).satisfied_by(ex),
{
    eventually_unfold::<T>(ex.suffix(i), p);
    let witness_idx = eventually_choose_witness(ex.suffix(i), p);
    execution_equality::<T>(ex.suffix(i).suffix(witness_idx), ex.suffix(i + witness_idx));
}

proof fn eventually_proved_by_witness<T>(ex: Execution<T>, p: TempPred<T>, witness_idx: nat)
    requires p.satisfied_by(ex.suffix(witness_idx)),
    ensures eventually(p).satisfied_by(ex)
{}

spec fn eventually_choose_witness<T>(ex: Execution<T>, p: TempPred<T>) -> nat
    recommends exists |i| p.satisfied_by(#[trigger] ex.suffix(i)),
{
    let witness = choose |i| p.satisfied_by(#[trigger] ex.suffix(i));
    witness
}

proof fn valid_p_implies_always_p<T>(p: TempPred<T>)
    requires valid(p),
    ensures valid(always(p)),
{
//    assert forall |ex| #[trigger] always(p).satisfied_by(ex) by {
////        assert(forall |i| #[trigger] p.satisfied_by(ex.suffix(i)));
//    };
}

proof fn always_distributed_by_and<T>(p: TempPred<T>, q: TempPred<T>)
    ensures valid(always(p.and(q)).implies(always(p).and(always(q)))),
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
        forall |idx: nat| inv(#[trigger] ex.suffix(idx).head()) && next(ex.suffix(idx).head(), ex.suffix(idx).head_next()) ==> inv(ex.suffix(idx).head_next()),
    ensures inv(ex.suffix(i).head()),
    decreases i,
{
    if i == 0 {
//        assert(init(ex.suffix(0).head()));
    } else {
        init_invariant_rec::<T>(ex, init, next, inv, (i-1) as nat);
    }
}

proof fn always_p_or_eventually_q_rec<T>(ex: Execution<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>, i: nat)
    requires
        forall |idx| p.satisfied_by(ex.suffix(idx)) && next.satisfied_by(ex.suffix(idx)) ==> p.satisfied_by(ex.suffix(idx + 1)) || q.satisfied_by(ex.suffix(idx + 1)),
        forall |idx| next.satisfied_by(#[trigger] ex.suffix(idx)),
        forall |idx| !q.satisfied_by(#[trigger] ex.suffix(idx)),
        p.satisfied_by(ex),
    ensures p.satisfied_by(ex.suffix(i)),
    decreases i,
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
    ensures always(p.implies(always(p).or(eventually(q)))).satisfied_by(ex),
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
    ensures inv.satisfied_by(ex.suffix(i)),
    decreases i,
{
    if i == 0 {
        execution_equality::<T>(ex, ex.suffix(0));
    } else {
        next_preserves_inv_rec::<T>(ex, next, inv, (i-1) as nat);
    }
}

proof fn instantiate_entailed_always<T>(ex: Execution<T>, i: nat, spec: TempPred<T>, p: TempPred<T>)
    requires
        spec.satisfied_by(ex),
        spec.implies(always(p)).satisfied_by(ex),
    ensures p.satisfied_by(ex.suffix(i)),
{
    implies_apply::<T>(ex, spec, always(p));
    always_unfold::<T>(ex, p);
}

proof fn instantiate_entailed_leads_to<T>(ex: Execution<T>, i: nat, spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.satisfied_by(ex),
        spec.implies(p.leads_to(q)).satisfied_by(ex),
    ensures p.implies(eventually(q)).satisfied_by(ex.suffix(i)),
{
    implies_apply::<T>(ex, spec, p.leads_to(q));
    leads_to_unfold::<T>(ex, p, q);
}

// All the lemmas above are used internally for proving the lemmas below
// The following lemmas are used by developers to simplify liveness/safety proof

pub proof fn always_implies_to_leads_to<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires spec.entails(always(p.implies(q))),
    ensures spec.entails(p.leads_to(q)),
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

pub proof fn execution_equality<T>(ex1: Execution<T>, ex2: Execution<T>)
    requires forall |i: nat| #[trigger] (ex1.nat_to_state)(i) == (ex2.nat_to_state)(i),
    ensures ex1 == ex2,
{
    assert(ex1.nat_to_state =~= ex2.nat_to_state);
    // fun_ext::<nat, T>(ex1.nat_to_state, ex2.nat_to_state);
}

pub proof fn temp_pred_equality<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        p.entails(q),
        q.entails(p),
    ensures p == q,
{
    assert forall |ex: Execution<T>| #[trigger] (p.pred)(ex) == (q.pred)(ex) by {
        if (p.pred)(ex) {
            implies_apply::<T>(ex, p, q);
        } else {
            implies_contraposition_apply::<T>(ex, q, p);
        }
    };
    assert(p.pred =~= q.pred);
    // fun_ext::<Execution<T>, bool>(p.pred, q.pred);
}

pub proof fn always_to_always_later<T>(spec: TempPred<T>, p: TempPred<T>)
    requires spec.entails(always(p)),
    ensures spec.entails(always(later(p))),
{
    assert forall |ex| #[trigger] always(p).satisfied_by(ex) implies always(later(p)).satisfied_by(ex) by {
        always_propagate_forwards(ex, p, 1);
        assert forall |i| #[trigger] later(p).satisfied_by(ex.suffix(i)) by {
            execution_equality(ex.suffix(i).suffix(1), ex.suffix(1).suffix(i));
        }
    }
    entails_trans(spec, always(p), always(later(p)));
}

proof fn always_double_equality<T>(p: TempPred<T>)
    ensures always(always(p)) == always(p),
{
    assert forall |ex| #[trigger] always(p).satisfied_by(ex) implies always(always(p)).satisfied_by(ex) by {
        assert forall |i| #[trigger] always(p).satisfied_by(ex.suffix(i)) by {
            assert forall |j| #[trigger] p.satisfied_by(ex.suffix(i).suffix(j)) by {
                execution_equality(ex.suffix(i).suffix(j), ex.suffix(i + j));
//                assert(p.satisfied_by(ex.suffix(i + j)));
            }
        }
    }
    assert forall |ex| #[trigger] always(always(p)).satisfied_by(ex) implies always(p).satisfied_by(ex) by {
        execution_equality(ex.suffix(0), ex);
//        assert(always(p).satisfied_by(ex.suffix(0)));
    }
    temp_pred_equality::<T>(always(always(p)), always(p));
}

pub proof fn always_and_equality<T>(p: TempPred<T>, q: TempPred<T>)
    ensures always(p.and(q)) == always(p).and(always(q)),
{
    assert forall |ex| #[trigger] always(p.and(q)).satisfied_by(ex) implies always(p).and(always(q)).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) by {
            always_unfold::<T>(ex, p.and(q));
        }
//        assert(always(p).satisfied_by(ex));
        assert forall |i| #[trigger] q.satisfied_by(ex.suffix(i)) by {
            always_unfold::<T>(ex, p.and(q));
        }
//        assert(always(q).satisfied_by(ex));
    };
    temp_pred_equality::<T>(always(p.and(q)), always(p).and(always(q)));
}

#[macro_export]
macro_rules! always_and_equality_n {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::always_and_equality_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! always_and_equality_n_internal {
    ($p1:expr, $p2:expr) => {
        always_and_equality($p1, $p2);
    };
    ($p1:expr, $p2:expr, $($tail:tt)*) => {
        always_and_equality($p1, $p2);
        always_and_equality_n_internal!($p1.and($p2), $($tail)*);
    };
}

pub use always_and_equality_n;
pub use always_and_equality_n_internal;

proof fn p_and_always_p_equals_always_p<T>(p: TempPred<T>)
    ensures p.and(always(p)) == always(p),
{
    assert forall |ex| #[trigger] always(p).satisfied_by(ex) implies p.and(always(p)).satisfied_by(ex) by {
        always_to_current::<T>(ex, p);
    };
    temp_pred_equality::<T>(p.and(always(p)), always(p));
}

proof fn a_to_temp_pred_equality<T, A>(p: spec_fn(A) -> TempPred<T>, q: spec_fn(A) -> TempPred<T>)
    requires forall |a: A| #[trigger] p(a).entails(q(a)) && q(a).entails(p(a)),
    ensures p == q,
{
    assert forall |a: A| #[trigger] p(a) == q(a) by {
        temp_pred_equality::<T>(p(a), q(a));
    };
    assert(p =~= q);
    // fun_ext::<A, TempPred<T>>(p, q);
}

proof fn tla_exists_equality<T, A>(f: spec_fn(A, T) -> bool)
    ensures lift_state(|t| exists |a| #[trigger] f(a, t)) == tla_exists(|a| lift_state(|t| f(a, t))),
{
    let p = lift_state(|t| exists |a| #[trigger] f(a, t));
    let q = tla_exists(|a| lift_state(|t| f(a, t)));

    let partial_p = |t| exists |a| #[trigger] f(a, t);
    let partial_q = |a| lift_state(|t| f(a, t));
    assert forall |ex| p.satisfied_by(ex) implies q.satisfied_by(ex) by {
//        assert(partial_p(ex.head()));
//        assert(exists |a| #[trigger] f(a, ex.head()));
        let witness_a = choose |a| #[trigger] f(a, ex.head());
        assert(partial_q(witness_a).satisfied_by(ex));
    };

    temp_pred_equality::<T>(p, q);
}

// Lift the "always" outside tla_forall if the function is previously wrapped by an "always"
// Note: Verus may not able to infer that (|a| func(a))(a) equals func(a).
//       Please turn to lemma tla_forall_always_equality_variant for troubleshooting.
pub proof fn tla_forall_always_equality<T, A>(a_to_p: spec_fn(A) -> TempPred<T>)
    ensures tla_forall(|a: A| always(a_to_p(a))) == always(tla_forall(a_to_p)),
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

pub proof fn tla_forall_always_equality_variant<T, A>(a_to_always: spec_fn(A) -> TempPred<T>, a_to_p: spec_fn(A) -> TempPred<T>)
    requires forall |a: A| #![trigger a_to_always(a)] a_to_always(a).entails((|a: A| always(a_to_p(a)))(a)) && ((|a: A| always(a_to_p(a)))(a)).entails(a_to_always(a)),
    ensures tla_forall(a_to_always) == always(tla_forall(a_to_p)),
{
    a_to_temp_pred_equality::<T, A>(a_to_always, |a: A| always(a_to_p(a)));
    temp_pred_equality::<T>(tla_forall(a_to_always), tla_forall(|a: A| always(a_to_p(a))));
    tla_forall_always_equality::<T, A>(a_to_p);
}

proof fn tla_forall_not_equality<T, A>(a_to_p: spec_fn(A) -> TempPred<T>)
    ensures tla_forall(|a: A| not(a_to_p(a))) == not(tla_exists(a_to_p)),
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

proof fn tla_forall_and_equality<T, A>(a_to_p: spec_fn(A) -> TempPred<T>, q: TempPred<T>)
    ensures tla_forall(|a: A| a_to_p(a).and(q)) == tla_forall(a_to_p).and(q),
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

pub proof fn tla_forall_apply<T, A>(a_to_p: spec_fn(A) -> TempPred<T>, a: A)
    ensures tla_forall(a_to_p).entails(a_to_p(a)),
{
//    assert forall |ex| #[trigger] tla_forall(a_to_p).satisfied_by(ex) implies a_to_p(a).satisfied_by(ex) by {
//        tla_forall_unfold::<T, A>(ex, a_to_p);
//    }
}

pub proof fn always_tla_forall_apply<T, A>(spec: TempPred<T>, a_to_p: spec_fn(A) -> TempPred<T>, a: A)
    requires spec.entails(always(tla_forall(a_to_p))),
    ensures spec.entails(always(a_to_p(a))),
{
    entails_preserved_by_always(tla_forall(a_to_p), a_to_p(a));
    entails_trans(spec, always(tla_forall(a_to_p)), always(a_to_p(a)));
}

proof fn tla_forall_or_equality<T, A>(a_to_p: spec_fn(A) -> TempPred<T>, q: TempPred<T>)
    ensures tla_forall(|a: A| a_to_p(a).or(q)) == tla_forall(a_to_p).or(q),
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

proof fn tla_exists_and_equality<T, A>(a_to_p: spec_fn(A) -> TempPred<T>, q: TempPred<T>)
    ensures tla_exists(|a: A| a_to_p(a).and(q)) == tla_exists(a_to_p).and(q),
{
    let a_to_p_and_q = |a: A| a_to_p(a).and(q);
    assert forall |ex| #[trigger] (tla_exists(a_to_p).and(q)).satisfied_by(ex)
    implies tla_exists(a_to_p_and_q).satisfied_by(ex) by {
        let witness_a = tla_exists_choose_witness::<T, A>(ex, a_to_p);
        tla_exists_proved_by_witness::<T, A>(ex, a_to_p_and_q, witness_a);
    };

    temp_pred_equality::<T>(tla_exists(|a: A| a_to_p(a).and(q)), tla_exists(a_to_p).and(q));
}

proof fn tla_exists_or_equality<T, A>(a_to_p: spec_fn(A) -> TempPred<T>, q: TempPred<T>)
    ensures tla_exists(|a: A| a_to_p(a).or(q)) == tla_exists(a_to_p).or(q),
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

proof fn tla_forall_implies_equality1<T, A>(a_to_p: spec_fn(A) -> TempPred<T>, q: TempPred<T>)
    ensures tla_forall(|a: A| a_to_p(a).implies(q)) == tla_exists(a_to_p).implies(q),
{
    let a_to_not_p = |a: A| not(a_to_p(a));
    a_to_temp_pred_equality::<T, A>(|a: A| a_to_p(a).implies(q), |a: A| a_to_not_p(a).or(q));
    temp_pred_equality::<T>(tla_forall(|a: A| a_to_p(a).implies(q)), tla_forall(|a: A| a_to_not_p(a).or(q)));
    tla_forall_or_equality::<T, A>(a_to_not_p, q);
    tla_forall_not_equality::<T, A>(a_to_p);
    temp_pred_equality::<T>(not(tla_exists(a_to_p)).or(q), tla_exists(a_to_p).implies(q));
}

proof fn tla_forall_implies_equality2<T, A>(p: TempPred<T>, a_to_q: spec_fn(A) -> TempPred<T>)
    ensures tla_forall(|a: A| p.implies(a_to_q(a))) == p.implies(tla_forall(a_to_q)),
{
    a_to_temp_pred_equality::<T, A>(|a: A| p.implies(a_to_q(a)), |a: A| a_to_q(a).or(not(p)));
    temp_pred_equality::<T>(tla_forall(|a: A| p.implies(a_to_q(a))), tla_forall(|a: A| a_to_q(a).or(not(p))));
    tla_forall_or_equality::<T, A>(a_to_q, not(p));
    temp_pred_equality::<T>(tla_forall(a_to_q).or(not(p)), p.implies(tla_forall(a_to_q)));
}

proof fn tla_exists_implies_equality1<T, A>(p: TempPred<T>, a_to_q: spec_fn(A) -> TempPred<T>)
    ensures tla_exists(|a: A| p.implies(a_to_q(a))) == p.implies(tla_exists(a_to_q)),
{
    a_to_temp_pred_equality::<T, A>(|a: A| p.implies(a_to_q(a)), |a: A| a_to_q(a).or(not(p)));
    temp_pred_equality::<T>(tla_exists(|a: A| p.implies(a_to_q(a))), tla_exists(|a: A| a_to_q(a).or(not(p))));
    tla_exists_or_equality::<T, A>(a_to_q, not(p));
    temp_pred_equality::<T>(tla_exists(a_to_q).or(not(p)), p.implies(tla_exists(a_to_q)));
}

proof fn tla_forall_leads_to_equality1<T, A>(a_to_p: spec_fn(A) -> TempPred<T>, q: TempPred<T>)
    ensures tla_forall(|a: A| a_to_p(a).leads_to(q)) == tla_exists(a_to_p).leads_to(q),
{
    tla_forall_always_equality_variant::<T, A>(|a: A| a_to_p(a).leads_to(q), |a: A| a_to_p(a).implies(eventually(q)));
    tla_forall_implies_equality1::<T, A>(a_to_p, eventually(q));
}

proof fn tla_forall_always_implies_equality2<T, A>(p: TempPred<T>, a_to_q: spec_fn(A) -> TempPred<T>)
    ensures tla_forall(|a: A| always(p.implies(a_to_q(a)))) == always(p.implies(tla_forall(a_to_q))),
{
    tla_forall_always_equality_variant::<T, A>(|a: A| always(p.implies(a_to_q(a))), |a: A| p.implies(a_to_q(a)));
    tla_forall_implies_equality2::<T, A>(p, a_to_q);
}

pub proof fn spec_entails_always_tla_forall<T, A>(spec: TempPred<T>, a_to_p: spec_fn(A)->TempPred<T>)
    requires forall |a: A| spec.entails(always(#[trigger] a_to_p(a))),
    ensures spec.entails(always(tla_forall(a_to_p))),
{
    let a_to_always = |a: A| always(a_to_p(a));
    spec_entails_tla_forall(spec, a_to_always);
    tla_forall_always_equality_variant::<T, A>(a_to_always, a_to_p);
}

pub proof fn spec_entails_tla_forall<T, A>(spec: TempPred<T>, a_to_p: spec_fn(A) -> TempPred<T>)
    requires forall |a: A| spec.entails(#[trigger] a_to_p(a)),
    ensures spec.entails(tla_forall(a_to_p)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies tla_forall(a_to_p).satisfied_by(ex) by {
        assert forall |a| #[trigger] a_to_p(a).satisfied_by(ex) by {
            implies_apply::<T>(ex, spec, a_to_p(a));
        };
    };
}

pub proof fn always_implies_forall_intro<T, A>(spec: TempPred<T>, p: TempPred<T>, a_to_q: spec_fn(A) -> TempPred<T>)
    requires forall |a: A| #[trigger] spec.entails(always(p.implies(a_to_q(a)))),
    ensures spec.entails(always(p.implies(tla_forall(a_to_q)))),
{
    let a_to_always_p_implies_q = |a: A| always(p.implies(a_to_q(a)));
    spec_entails_tla_forall::<T, A>(spec, a_to_always_p_implies_q);
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(p.implies(tla_forall(a_to_q))).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, tla_forall(a_to_always_p_implies_q));
        tla_forall_always_implies_equality2::<T, A>(p, a_to_q)
    };
}

pub proof fn leads_to_exists_intro<T, A>(spec: TempPred<T>, a_to_p: spec_fn(A) -> TempPred<T>, q: TempPred<T>)
    requires forall |a: A| #[trigger] spec.entails(a_to_p(a).leads_to(q)),
    ensures spec.entails(tla_exists(a_to_p).leads_to(q)),
{
    let a_to_p_leads_to_q = |a: A| a_to_p(a).leads_to(q);
    spec_entails_tla_forall::<T, A>(spec, a_to_p_leads_to_q);
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies tla_exists(a_to_p).leads_to(q).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, tla_forall(a_to_p_leads_to_q));
        tla_forall_leads_to_equality1::<T, A>(a_to_p, q);
    };
}

// This lemmas instantiates tla_forall for a.
pub proof fn use_tla_forall<T, A>(spec: TempPred<T>, a_to_p: spec_fn(A) -> TempPred<T>, a: A)
    requires spec.entails(tla_forall(a_to_p)),
    ensures spec.entails(a_to_p(a)),
{
    assert forall |ex: Execution<T>| #[trigger] spec.satisfied_by(ex) implies (a_to_p(a)).satisfied_by(ex) by {
        entails_apply(ex, spec, tla_forall(a_to_p));
//        assert(spec.implies(tla_forall(a_to_p)).satisfied_by(ex));
    };
}

// Obviously p ~> p is valid
// post:
//     |= p ~> p
pub proof fn leads_to_self_temp<T>(p: TempPred<T>)
    ensures valid(p.leads_to(p)),
{
    assert forall |ex| #[trigger] always(p.implies(eventually(p))).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(p).satisfied_by(ex.suffix(i)) by {
            execution_equality::<T>(ex.suffix(i), ex.suffix(i).suffix(0));
            eventually_proved_by_witness::<T>(ex.suffix(i), p, 0);
        };
    };
}

// Entails p if entails always p
// pre:
//     spec |= []p
// post:
//     spec |= p
pub proof fn eliminate_always<T>(spec: TempPred<T>, p: TempPred<T>)
    requires spec.entails(always(p)),
    ensures spec.entails(p),
{
    assert forall |ex| spec.satisfied_by(ex) implies #[trigger] p.satisfied_by(ex) by {
        implies_apply(ex, spec, always(p));
        execution_equality(ex, ex.suffix(0));
    }
}

// Entails p and q if entails each of them.
// pre:
//     spec |= p
//     spec |= q
// post:
//     spec |= p && q
pub proof fn entails_and_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(p),
        spec.entails(q),
    ensures spec.entails(p.and(q)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.and(q).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, p);
        implies_apply::<T>(ex, spec, q);
    };
}

// Entails the conjunction of all the p if entails each of them.
// pre:
//     spec |= p1
//     spec |= p2
//        ...
//     spec |= pn
// post:
//     spec |= p1 /\ p2 /\ ... /\ pn
//
// Usage: entails_and_n!(spec, p1, p2, p3, p4)
#[macro_export]
macro_rules! entails_and_n {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::entails_and_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! entails_and_n_internal {
    ($spec:expr, $p1:expr, $p2:expr) => {
        entails_and_temp($spec, $p1, $p2);
    };
    ($spec:expr, $p1:expr, $p2:expr, $($tail:tt)*) => {
        entails_and_temp($spec, $p1, $p2);
        entails_and_n_internal!($spec, $p1.and($p2), $($tail)*);
    };
}

pub use entails_and_n;
pub use entails_and_n_internal;

// Entails always the conjunction of all the p if entails each always p.
// pre:
//     spec |= []p1
//     spec |= []p2
//        ...
//     spec |= []pn
// post:
//     spec |= [](p1 /\ p2 /\ ... /\ pn)
//
// Usage: entails_always_and_n!(spec, p1, p2, p3, p4)
#[macro_export]
macro_rules! entails_always_and_n {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::entails_always_and_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! entails_always_and_n_internal {
    ($spec:expr, $p1:expr) => {};
    ($spec:expr, $p1:expr, $p2:expr) => {
        entails_and_temp($spec, always($p1), always($p2));
        always_and_equality($p1, $p2);
    };
    ($spec:expr, $p1:expr, $p2:expr, $($tail:tt)*) => {
        entails_and_temp($spec, always($p1), always($p2));
        always_and_equality($p1, $p2);
        entails_always_and_n_internal!($spec, $p1.and($p2), $($tail)*);
    };
}

pub use entails_always_and_n;
pub use entails_always_and_n_internal;

// Merge the next and other state predicates together into one action predicate.
// Usage:
// Given next, p1, p2, p3, ...,
// returns |s, s_prime| next(s, s_prime) && p1(s) && p2(s) && p3(s) && ...
//
// Note: Verus reports strange errors saying the returned closure is not a spec_fn
#[macro_export]
macro_rules! merge_into_next {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::merge_into_next_internal!($($tail)*))
    }
}

#[macro_export]
macro_rules! merge_into_next_internal {
    ($next:expr, $($expr:expr),* $(,)?) => {
        |s, s_prime| {
            $next(s, s_prime) &&
            $(
                $expr(s) &&
            )*
            true
        }
    };
}

pub use merge_into_next;
pub use merge_into_next_internal;

// Combine the temporal predicates together using and.
// Usage:
// Given next, p1, p2, p3, ...,
// returns next.and(p1).and(p2).and(p3)...
#[macro_export]
macro_rules! combine_with_next {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::combine_with_next_internal!($($tail)*))
    }
}

#[macro_export]
macro_rules! combine_with_next_internal {
    ($next:expr) => {
        $next
    };
    ($next:expr, $($expr:expr),* $(,)?) => {
        $next $(
            .and($expr)
        )*
    };
}

pub use combine_with_next;
pub use combine_with_next_internal;

// Strengthen next with arbitrary number of predicates.
// pre:
//     spec |= []p1
//     spec |= []p2
//        ...
//     spec |= []pn
//     p1 /\ p2 /\ ... /\ pn ==> partial_spec
// post:
//     spec |= []all
//
// Usage: combine_spec_entails_always_n!(spec, partial_spec, p1, p2, p3, p4)
#[macro_export]
macro_rules! combine_spec_entails_always_n {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::combine_spec_entails_always_n_internal!($($tail)*))
    }
}

#[macro_export]
macro_rules! combine_spec_entails_always_n_internal {
    ($spec:expr, $partial_spec:expr, $($tail:tt)*) => {
        assert_by(
            valid($spec.implies(always(combine_with_next!($($tail)*)))),
            {
                entails_always_and_n!($spec, $($tail)*);
            }
        );
        entails_preserved_by_always(combine_with_next!($($tail)*), $partial_spec);
        entails_trans($spec, always(combine_with_next!($($tail)*)), always($partial_spec));
    };
}

pub use combine_spec_entails_always_n;
pub use combine_spec_entails_always_n_internal;

// Show that an spec entails the invariant by a group of action/state predicates which are also invariants entailed by spec.
// pre:
//     partial_spec |= inv
//     spec |= []p1
//     spec |= []p2
//         ...
//     spec |= []pn
//     p1 /\ p2 /\ ... /\ pn ==> partial_spec
// post:
//     spec |= []inv
//
// Usage: invariant_n!(spec, partial_spec, inv, p1, p2, ..., pn)
#[macro_export]
macro_rules! invariant_n {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::invariant_n_internal!($($tail)*))
    }
}

#[macro_export]
macro_rules! invariant_n_internal {
    ($spec:expr, $partial_spec:expr, $inv:expr, $($tail:tt)*) => {
        assert_by(
            valid($spec.implies(always(combine_with_next!($($tail)*)))),
            {
                entails_always_and_n!($spec, $($tail)*);
            }
        );
        entails_preserved_by_always(combine_with_next!($($tail)*), $partial_spec);
        entails_trans($spec, always(combine_with_next!($($tail)*)), always($partial_spec));
        entails_preserved_by_always($partial_spec, $inv);
        entails_trans($spec, always($partial_spec), always($inv));
    };
}

pub use invariant_n;
pub use invariant_n_internal;

// Combining two specs together entails p and q if each of them entails p, q respectively.
// pre:
//     spec1 |= p
//     spec2 |= q
// post:
//     spec1 /\ spec2 |= p /\ q
pub proof fn entails_and_different_temp<T>(spec1: TempPred<T>, spec2: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec1.entails(p),
        spec2.entails(q),
    ensures spec1.and(spec2).entails(p.and(q)),
{
    assert forall |ex| #[trigger] spec1.and(spec2).satisfied_by(ex) implies p.and(q).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec1, p);
        implies_apply::<T>(ex, spec2, q);
    };
}

// An always predicate is stable.
// post:
//     |= stable(always(p))
pub proof fn always_p_is_stable<T>(p: TempPred<T>)
    ensures valid(stable(always(p))),
{
    assert forall |ex| #[trigger] always(p).satisfied_by(ex) implies always(always(p)).satisfied_by(ex) by {
        assert forall |i| #[trigger] always(p).satisfied_by(ex.suffix(i)) by {
            always_propagate_forwards::<T>(ex, p, i);
        }
    }
}

// A leads-to predicate is stable.
// post:
//     |= stable(p ~> q)
pub proof fn p_leads_to_q_is_stable<T>(p: TempPred<T>, q: TempPred<T>)
    ensures
        valid(stable(p.leads_to(q))),
{
    always_p_is_stable(p.implies(eventually(q)));
}

// Forall a leads-to predicate p -> q(a) is stable.
// pre:
//     forall |a| |= stable(p -> q(a))
// post:
//     |= stable(tla_forall(|a| p -> q(a)))
pub proof fn tla_forall_a_p_leads_to_q_a_is_stable<T, A>(p: TempPred<T>, a_to_q: spec_fn(A) -> TempPred<T>)
    requires forall |a: A| #[trigger] valid(stable(p.leads_to(a_to_q(a)))),
    ensures valid(stable(tla_forall(|a: A| p.leads_to(a_to_q(a))))),
{
    let target = tla_forall(|a: A| p.leads_to(a_to_q(a)));
    assert forall |ex| (forall |a: A| #[trigger] valid(stable(p.leads_to(a_to_q(a))))) implies #[trigger] stable(target).satisfied_by(ex) by {
        assert forall |i| (forall |a: A| #[trigger] valid(stable(p.leads_to(a_to_q(a))))) implies 
                    (target.satisfied_by(ex) ==> #[trigger] target.satisfied_by(ex.suffix(i))) by {
            assert forall |a: A| (forall |a: A| #[trigger] valid(stable(p.leads_to(a_to_q(a))))) implies 
                        (p.leads_to(a_to_q(a)).satisfied_by(ex) ==> #[trigger] p.leads_to(a_to_q(a)).satisfied_by(ex.suffix(i))) by {
                assert(valid(stable(p.leads_to(a_to_q(a)))));
                assert(stable(p.leads_to(a_to_q(a))).satisfied_by(ex));
                if (p.leads_to(a_to_q(a)).satisfied_by(ex)) {
//                    assert(p.leads_to(a_to_q(a)).satisfied_by(ex.suffix(i)));
                }
            }
        }
    }
}

// p and q is stable if both p and q are stable.
// pre:
//     |= stable(p)
//     |= stable(q)
// post:
//     |= stable(p /\ q)
pub proof fn stable_and_temp<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        valid(stable(p)),
        valid(stable(q)),
    ensures valid(stable(p.and(q))),
{
    assert forall |ex| #[trigger] p.and(q).satisfied_by(ex) implies always(p.and(q)).satisfied_by(ex) by {
        stable_unfold::<T>(ex, p);
        stable_unfold::<T>(ex, q);
    }
}

// The conjunction of all the p is stable if each p is stable.
// pre:
//     |= stable(p1)
//     |= stable(p2)
//      ...
//     |= stable(pn)
// post:
//     |= stable(p1 /\ p2 /\ ... /\ pn)
//
// Usage: stable_and_n!(p1, p2, p3, p4)
#[macro_export]
macro_rules! stable_and_n {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::stable_and_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! stable_and_n_internal {
    ($p1:expr, $p2:expr) => {
        stable_and_temp($p1, $p2);
    };
    ($p1:expr, $p2:expr, $($tail:tt)*) => {
        stable_and_temp($p1, $p2);
        stable_and_n_internal!($p1.and($p2), $($tail)*);
    };
}

pub use stable_and_n;
pub use stable_and_n_internal;

// The conjunction of all the p is stable if each p is stable.
// post:
//     |= stable(always(p1) /\ always(p2) /\ ... /\ always(pn))
//
// Usage: stable_and_always_n!(p1, p2, p3, p4)
#[macro_export]
macro_rules! stable_and_always_n {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::stable_and_always_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! stable_and_always_n_internal {
    ($p1:expr, $($tail:expr),*) => {
        always_p_is_stable($p1);
        $(always_p_is_stable($tail);)*
        stable_and_n!(always($p1), $(always($tail)),*);
    };
}

pub use stable_and_always_n;
pub use stable_and_always_n_internal;

// Unpack the conditions from the left to the right side of |=
// pre:
//     |= stable(spec)
//     spec /\ c |= p ~> q
// post:
//     spec |= p /\ c ~> q
pub proof fn unpack_conditions_from_spec<T>(spec: TempPred<T>, c: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        valid(stable(spec)),
        spec.and(c).entails(p.leads_to(q)),
    ensures spec.entails(p.and(c).leads_to(q)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.and(c).leads_to(q).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.and(c).satisfied_by(ex.suffix(i)) implies eventually(q).satisfied_by(ex.suffix(i)) by {
            stable_unfold::<T>(ex, spec);
            implies_apply::<T>(ex.suffix(i), spec.and(c), p.leads_to(q));
            leads_to_unfold::<T>(ex.suffix(i), p, q);
            execution_equality::<T>(ex.suffix(i), ex.suffix(i).suffix(0));
            implies_apply::<T>(ex.suffix(i), p, eventually(q));
        };
    };
}

// Pack the conditions from the right to the left side of |=
// pre:
//     spec |= p /\ c ~> q
// post:
//     spec /\ []c |= p ~> q
proof fn pack_conditions_to_spec<T>(spec: TempPred<T>, c: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires spec.entails(p.and(c).leads_to(q)),
    ensures spec.and(always(c)).entails(p.leads_to(q)),
{
    assert forall |ex| #[trigger] spec.and(always(c)).satisfied_by(ex) implies p.leads_to(q).satisfied_by(ex) by {
        implies_apply(ex, spec, p.and(c).leads_to(q));
        leads_to_unfold(ex, p.and(c), q);
//        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(q).satisfied_by(ex.suffix(i)) by {
//            always_propagate_forwards(ex, c, i);
//            implies_apply(ex.suffix(i), p.and(c), eventually(q));
//        }
    }
}

// This lemma is used to make the predicate as concise as possible.
// Similar to the first-order logic where p equals p /\ q when p -> q is satisfied,
// we can reduce the size of predicate when some part of it implies the rest.
// pre:
//     p |= q
// post:
//     p == p /\ q
pub proof fn simplify_predicate<T>(p: TempPred<T>, q: TempPred<T>)
    requires p.entails(q),
    ensures p == p.and(q),
{
    assert forall |ex| #[trigger] p.satisfied_by(ex) implies p.and(q).satisfied_by(ex) by {
        entails_and_temp::<T>(p, p, q);
        entails_apply::<T>(ex, p, p.and(q));
    };
    temp_pred_equality::<T>(p, p.and(q));
}

// Prove safety by induction.
// pre:
//     |= init => inv
//     |= inv /\ next => inv'
//     spec |= init /\ []next
// post:
//     spec |= []inv
pub proof fn init_invariant<T>(spec: TempPred<T>, init: StatePred<T>, next: ActionPred<T>, inv: StatePred<T>)
    requires
        forall |s: T| #[trigger] init(s) ==> inv(s),
        forall |s, s_prime: T| inv(s) && #[trigger] next(s, s_prime) ==> inv(s_prime),
        spec.entails(lift_state(init)),
        spec.entails(always(lift_action(next))),
    ensures spec.entails(always(lift_state(inv))),
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

// Strengthen next with inv.
// pre:
//     spec |= []next
//     spec |= []inv
//     |= next /\ inv <=> next_and_inv
// post:
//     spec |= []next_and_inv
pub proof fn strengthen_next<T>(spec: TempPred<T>, next: ActionPred<T>, inv: StatePred<T>, next_and_inv: ActionPred<T>)
    requires
        spec.entails(always(lift_action(next))),
        spec.entails(always(lift_state(inv))),
        lift_action(next_and_inv).entails(lift_action(next).and(lift_state(inv))),
        lift_action(next).and(lift_state(inv)).entails(lift_action(next_and_inv)),
    ensures spec.entails(always(lift_action(next_and_inv))),
{
    entails_and_temp::<T>(spec, always(lift_action(next)), always(lift_state(inv)));
    always_and_equality::<T>(lift_action(next), lift_state(inv));
    temp_pred_equality::<T>(lift_action(next_and_inv), lift_action(next).and(lift_state(inv)));
}

// Get the initial leads_to.
// pre:
//     spec |= [](p /\ next => p' \/ q')
//     spec |= [](p /\ next /\ forward => q')
//     spec |= []next
//     spec |= []p ~> forward
// post:
//     spec |= p ~> q
pub proof fn wf1_variant_temp<T>(spec: TempPred<T>, next: TempPred<T>, forward: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(p.and(next).implies(later(p).or(later(q))))),
        spec.entails(always(p.and(next).and(forward).implies(later(q)))),
        spec.entails(always(next)),
        spec.entails(always(p).leads_to(forward)),
    ensures spec.entails(p.leads_to(q)),
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

// Get the initial leads_to with a stronger wf assumption than wf1_variant.
// pre:
//     |= p /\ next => p' \/ q'
//     |= p /\ next /\ forward => q'
//     |= p => enabled(forward)
//     spec |= []next
//     spec |= wf(forward)
// post:
//     spec |= p ~> q
pub proof fn wf1<T>(spec: TempPred<T>, next: ActionPred<T>, forward: ActionPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        forall |s, s_prime: T| p(s) && #[trigger] next(s, s_prime) ==> p(s_prime) || q(s_prime),
        forall |s, s_prime: T| p(s) && #[trigger] next(s, s_prime) && forward(s, s_prime) ==> q(s_prime),
        forall |s: T| #[trigger] p(s) ==> enabled(forward)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(weak_fairness(forward)),
    ensures spec.entails(lift_state(p).leads_to(lift_state(q))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(lift_state(p)).leads_to(lift_action(forward)).satisfied_by(ex) by {
        assert forall |i| #[trigger] always(lift_state(p)).satisfied_by(ex.suffix(i)) implies eventually(lift_action(forward)).satisfied_by(ex.suffix(i)) by {
//            assert(always(lift_state(p).implies(lift_state(enabled(forward)))).satisfied_by(ex.suffix(i)));
            implies_apply_with_always::<T>(ex.suffix(i), lift_state(p), lift_state(enabled(forward)));
            execution_equality::<T>(ex.suffix(i).suffix(0), ex.suffix(i));

            implies_apply::<T>(ex, spec, weak_fairness(forward));
            weak_fairness_unfold::<T>(ex, forward);
            implies_apply::<T>(ex.suffix(i), lift_state(enabled(forward)), eventually(lift_action(forward)));
        };
    };
    wf1_variant_temp::<T>(spec, lift_action(next), lift_action(forward), lift_state(p), lift_state(q));
}

// Connects two valid implies.
// pre:
//     p |= q
//     q |= r
// post:
//     p |= r
pub proof fn entails_trans<T>(p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        p.entails(q),
        q.entails(r),
    ensures p.entails(r),
{
    assert forall |ex| p.satisfied_by(ex) implies r.satisfied_by(ex) by {
        implies_apply::<T>(ex, p, q);
        implies_apply::<T>(ex, q, r);
    };
}

// If p implies q for all executions, p will leads to q anyway.
// pre:
//     p |= q
// post:
//     spec |= p ~> q
// Note: there is no constraint on spec, it can be true_pred().
pub proof fn entails_implies_leads_to<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires p.entails(q),
    ensures spec.entails(p.leads_to(q)),
{
    valid_p_implies_always_p(p.implies(q));
    always_implies_to_leads_to(spec, p, q);
}

// Introduce always to both sides of implies.
// pre:
//     p |= q
// post:
//     []p |= []q
pub proof fn entails_preserved_by_always<T>(p: TempPred<T>, q: TempPred<T>)
    requires p.entails(q),
    ensures always(p).entails(always(q)),
{
    assert forall |ex| always(p).satisfied_by(ex) implies always(q).satisfied_by(ex) by {
        assert forall |i:nat| q.satisfied_by(#[trigger] ex.suffix(i)) by {
            always_unfold::<T>(ex, p);
            implies_apply::<T>(ex.suffix(i), p, q);
        };
    };
}

// Weaken always by implies.
// pre:
//     |= p => q
//     spec |= []p
// post:
//     spec |= []q
pub proof fn always_weaken<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        valid(p.implies(q)),
        spec.entails(always(p)),
    ensures spec.entails(always(q)),
{
    entails_preserved_by_always::<T>(p, q);
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(q).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, always(p));
        implies_apply::<T>(ex, always(p), always(q));
    };
}

// Introduce always to both sides of always implies.
// pre:
//     spec |= [](p => q)
// post:
//     spec |= []([]p => []q)
pub proof fn always_implies_preserved_by_always<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires spec.entails(always(p.implies(q))),
    ensures spec.entails(always(always(p).implies(always(q)))),
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

// Enhance the conclusion of leads to always using invariant.
// pre:
//     spec |= []inv
//     spec |= p ~> []q1
//     q1 /\ inv |= q2
// post:
//     spec |= p ~> []q2
pub proof fn leads_to_always_enhance<T>(spec: TempPred<T>, inv: TempPred<T>, p: TempPred<T>, q1: TempPred<T>, q2: TempPred<T>)
    requires
        spec.entails(always(inv)),
        spec.entails(p.leads_to(always(q1))),
        q1.and(inv).entails(q2),
    ensures spec.entails(p.leads_to(always(q2))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(always(q2)).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i))
        implies eventually(always(q2)).satisfied_by(ex.suffix(i)) by {
            implies_apply(ex, spec, always(inv));
            implies_apply(ex, spec, p.leads_to(always(q1)));
            leads_to_unfold(ex, p, always(q1));
            implies_apply(ex.suffix(i), p, eventually(always(q1)));
            let witness = eventually_choose_witness(ex.suffix(i), always(q1));
            assert forall |j| #[trigger] q2.satisfied_by(ex.suffix(i).suffix(witness).suffix(j)) by {
                execution_equality(ex.suffix(i).suffix(witness).suffix(j), ex.suffix(i + witness + j));
                implies_apply(ex.suffix(i).suffix(witness).suffix(j), q1.and(inv), q2);
            }
            eventually_proved_by_witness(ex.suffix(i), always(q2), witness);
        }
    }
}

// Get eventually from leads_to.
// pre:
//     spec |= p
//     spec |= p ~> q
// post:
//     spec |= <>q
pub proof fn leads_to_apply<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(p),
        spec.entails(p.leads_to(q)),
    ensures spec.entails(eventually(q)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies eventually(q).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, p);
        implies_apply::<T>(ex, spec, p.leads_to(q));
        leads_to_unfold::<T>(ex, p, q);
        execution_equality::<T>(ex, ex.suffix(0));
        implies_apply::<T>(ex, p, eventually(q));
    };
}

// Connect two leads_to by transitivity.
// pre:
//     spec |= p ~> q
//     spec |= q ~> r
// post:
//     spec |= p ~> r
pub proof fn leads_to_trans<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.leads_to(q)),
        spec.entails(q.leads_to(r)),
    ensures spec.entails(p.leads_to(r)),
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

#[macro_export]
macro_rules! leads_to_trans_n {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::leads_to_trans_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! leads_to_trans_n_internal {
    ($spec:expr, $p1:expr, $p2:expr, $p3:expr) => {
        leads_to_trans($spec, $p1, $p2, $p3);
    };
    ($spec:expr, $p1:expr, $p2:expr, $p3:expr, $($tail:tt)*) => {
        leads_to_trans($spec, $p1, $p2, $p3);
        leads_to_trans_n_internal!($spec, $p1, $p3, $($tail)*);
    };
}

pub use leads_to_trans_n;
pub use leads_to_trans_n_internal;

// Weaken leads_to by implies.
// pre:
//     spec |= [](p2 => p1)
//     spec |= [](q1 => q2)
//     spec |= p1 ~> q1
// post:
//     spec |= p2 ~> q2
pub proof fn leads_to_weaken<T>(spec: TempPred<T>, p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>)
    requires
        spec.entails(always(p2.implies(p1))),
        spec.entails(always(q1.implies(q2))),
        spec.entails(p1.leads_to(q1)),
    ensures spec.entails(p2.leads_to(q2)),
{
    always_implies_to_leads_to::<T>(spec, p2, p1);
    always_implies_to_leads_to::<T>(spec, q1, q2);
    leads_to_trans::<T>(spec, p2, p1, q1);
    leads_to_trans::<T>(spec, p2, q1, q2);
}

// Combine the premises of two leads_to using or.
// pre:
//     spec |= p ~> r
//     spec |= q ~> r
// post:
//     spec |= (p \/ q) ~> r
pub proof fn or_leads_to_combine<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.leads_to(r)),
        spec.entails(q.leads_to(r)),
    ensures spec.entails(p.or(q).leads_to(r)),
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

// Combine the premises of all the leads_to using or.
// pre:
//     spec |= p1 ~> q
//     spec |= p2 ~> q
//         ...
//     spec |= pn ~> q
// post:
//     spec |= (p1 \/ p2 \/ ... \/ pn) ~> q
//
// Usage: or_leads_to_combine_n!(spec, p1, p2, p3, p4; q)
#[macro_export]
macro_rules! or_leads_to_combine_n {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::or_leads_to_combine_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! or_leads_to_combine_n_internal {
    ($spec:expr, $p1:expr, $p2:expr; $q:expr) => {
        or_leads_to_combine($spec, $p1, $p2, $q);
    };
    ($spec:expr, $p1:expr, $p2:expr, $($rest:expr),+; $q:expr) => {
        or_leads_to_combine($spec, $p1, $p2, $q);
        or_leads_to_combine_n_internal!($spec, $p1.or($p2), $($rest),+; $q);
    };
}

pub use or_leads_to_combine_n;
pub use or_leads_to_combine_n_internal;

// Combine or_leads_to_combine and temp_pred_equality.
// The 'result' is the equivalent temporal predicate of joining all following predicates with \/.
#[macro_export]
macro_rules! or_leads_to_combine_and_equality {
    ($spec:expr, $result:expr, $p1:expr, $($rest:expr),+; $q:expr) => {
        temp_pred_equality(
            $result,
            $p1$(.or($rest))+
        );
        or_leads_to_combine_n!($spec, $p1, $($rest),+; $q);
    }
}

pub use or_leads_to_combine_and_equality;

// Leads to the conjunction of all the []q if leads to each of them.
// pre:
//     spec |= p ~> []q1
//     spec |= p ~> []q2
//        ...
//     spec |= p ~> []qn
// post:
//     spec |= p ~> [](q1 /\ q2 /\ ... /\ qn)
//
// Usage: leads_to_always_combine_n!(spec, p, q1, q2, q3, q4)
#[macro_export]
macro_rules! leads_to_always_combine_n {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::leads_to_always_combine_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! leads_to_always_combine_n_internal {
    ($spec:expr, $p:expr, $q1:expr, $q2:expr) => {
        leads_to_always_combine($spec, $p, $q1, $q2);
    };
    ($spec:expr, $p:expr, $q1:expr, $q2:expr, $($tail:tt)*) => {
        leads_to_always_combine($spec, $p, $q1, $q2);
        always_and_equality($q1, $q2);
        leads_to_always_combine_n_internal!($spec, $p, $q1.and($q2), $($tail)*);
    };
}

pub use leads_to_always_combine_n;
pub use leads_to_always_combine_n_internal;

#[macro_export]
macro_rules! leads_to_always_combine_n_with_equality {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::leads_to_always_combine_n_with_equality_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! leads_to_always_combine_n_with_equality_internal {
    ($spec:expr, $p:expr, $dst:expr, $($tail:tt)*) => {
        temp_pred_equality($dst, combine_with_next!($($tail)*));
        leads_to_always_combine_n!($spec, $p, $($tail)*);
    };
}

pub use leads_to_always_combine_n_with_equality;
pub use leads_to_always_combine_n_with_equality_internal;

// Leads to []tla_forall(a_to_p) if forall a, it leads []a_to_p(a).
// pre:
//     forall |a: A|, spec |= p ~> []a_to_p(a)
//     forall |a: A|, a \in domain
//     domain.is_finite() && domain.len() > 0
// post:
//     spec |= []tla_forall(a_to_p)
// The domain set assist in showing type A contains finite elements.
//
// This lemma is actually similar to leads_to_always_combine_n when the n predicates are all a_to_p(a) for some a.
// This is because tla_forall(a_to_p) == a_to_p(a1).and(a_to_p(a2))....and(a_to_p(an)), We only consider the case when
// type A is finite here.
pub proof fn leads_to_always_tla_forall<T, A>(spec: TempPred<T>, p: TempPred<T>, a_to_p: spec_fn(A)->TempPred<T>, domain: Set<A>)
    requires
        forall |a: A| spec.entails(p.leads_to(always(#[trigger] a_to_p(a)))),
        domain.finite(),
        domain.len() > 0,
        forall |a: A| #[trigger] domain.contains(a),
    ensures spec.entails(p.leads_to(always(tla_forall(a_to_p)))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(always(tla_forall(a_to_p))).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(always(tla_forall(a_to_p))).satisfied_by(ex.suffix(i)) by {
            assert forall |a: A| p.leads_to(always(#[trigger] a_to_p(a))).satisfied_by(ex) by {
                implies_apply::<T>(ex, spec, p.leads_to(always(a_to_p(a))));
            }
            assert forall |a: A| eventually(always(#[trigger] a_to_p(a))).satisfied_by(ex.suffix(i)) by {
                implies_apply::<T>(ex.suffix(i), p, eventually(always(a_to_p(a))));
            }

            let a_to_witness = Map::new(|a: A| domain.contains(a), |a: A| {
                let wit = eventually_choose_witness::<T>(ex.suffix(i), always(a_to_p(a)));
                wit
            });
//            assert(a_to_witness.dom() =~= domain);
            assert(a_to_witness.dom() == domain);
//            assert(a_to_witness.dom().finite());
//            assert(a_to_witness.dom().len() > 0);
            let r = |a1: nat, a2: nat| a1 <= a2;
            let values = a_to_witness.values();
            lemma_values_finite(a_to_witness);
            assert_by(
                values.len() > 0, {
                let x = a_to_witness.dom().choose();
//                assert(a_to_witness.contains_key(x));
//                assert(a_to_witness.contains_value(a_to_witness[x]));
                assert(values.contains(a_to_witness[x]));
            });
            let max_witness = values.find_unique_maximal(r);
            values.find_unique_maximal_ensures(r);
            values.lemma_maximal_equivalent_greatest(r, max_witness);

            assert forall |a: A| always(#[trigger] a_to_p(a)).satisfied_by(ex.suffix(i).suffix(max_witness)) by {
//                assert(domain.contains(a));
//                assert(vstd::relations::is_greatest(r, max_witness, values));
                let witness = a_to_witness[a];
                assert(r(witness, max_witness));
//                assert(max_witness >= witness);
                always_propagate_forwards::<T>(ex.suffix(i).suffix(witness), a_to_p(a), (max_witness - witness) as nat);
                execution_equality::<T>(ex.suffix(i).suffix(max_witness), ex.suffix(i).suffix(witness).suffix((max_witness - witness) as nat));
            }
            eventually_proved_by_witness(ex.suffix(i), always(tla_forall(a_to_p)), max_witness);
        };
    };
}

// Combine the conclusions of two leads_to if the conclusions are stable.
// pre:
//     spec |= p ~> []q
//     spec |= p ~> []r
// post:
//     spec |= p ~> [](q /\ r)
pub proof fn leads_to_always_combine<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.leads_to(always(q))),
        spec.entails(p.leads_to(always(r))),
    ensures
        spec.entails(p.leads_to(always(q.and(r)))),
        spec.entails(p.leads_to(always(q).and(always(r)))),
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
    always_and_equality(q, r);
}

// Prove p leads_to always q by showing that q is preserved.
// pre:
//     spec |= [](q /\ next => q')
//     spec |= []next
//     spec |= p ~> q
// post:
//     spec |= p ~> []q
pub proof fn leads_to_stable<T>(spec: TempPred<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(q.and(next).implies(later(q)))),
        spec.entails(always(next)),
        spec.entails(p.leads_to(q)),
    ensures spec.entails(p.leads_to(always(q))),
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

// Sandwich leads-to with or r.
// pre:
//     spec |= p ~> q
// post:
//     spec |= p \/ r ~> q \/ r
pub proof fn leads_to_framed_by_or<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires spec.entails(p.leads_to(q)),
    ensures spec.entails(p.or(r).leads_to(q.or(r))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.or(r).leads_to(q.or(r)).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.or(r).satisfied_by(ex.suffix(i)) implies eventually(q.or(r)).satisfied_by(ex.suffix(i)) by {
            implies_apply(ex, spec, p.leads_to(q));
            leads_to_unfold(ex, p, q);
            if p.satisfied_by(ex.suffix(i)) {
                implies_apply(ex.suffix(i), p, eventually(q));
                let witness_idx = eventually_choose_witness(ex.suffix(i), q);
                eventually_proved_by_witness(ex.suffix(i), q.or(r), witness_idx);
            } else {
                let witness_idx = 0;
                execution_equality(ex.suffix(i), ex.suffix(i).suffix(0));
                eventually_proved_by_witness(ex.suffix(i), q.or(r), witness_idx);
            }
        }
    }
}

// Combine two leads-to with a shortcut.
// pre:
//     spec |= p ~> q \/ s
//     spec |= q ~> r \/ s
// post:
//     spec |= p ~> r \/ s
pub proof fn leads_to_shortcut_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>, s: TempPred<T>)
    requires
        spec.entails(p.leads_to(q.or(s))),
        spec.entails(q.leads_to(r.or(s))),
    ensures spec.entails(p.leads_to(r.or(s))),
{
    leads_to_framed_by_or(spec, q, r.or(s), s);
    temp_pred_equality(r.or(s).or(s), r.or(s));
    leads_to_trans(spec, p, q.or(s), r.or(s));
}

// Concluding p(n) ~> p(0) using ranking functions, with a step of one.
// pre:
//     forall |n: nat|, n > 0 ==> spec |= p(n) ~> p(n - 1)
// post:
//     forall |n: nat|, spec |= p(n) ~> p(0).
pub proof fn leads_to_rank_step_one<T>(spec: TempPred<T>, p: spec_fn(nat) -> TempPred<T>)
    requires
        forall |n: nat| #![trigger p(n)] (n > 0 ==> spec.entails(p(n).leads_to(p((n - 1) as nat)))),
    ensures
        forall |n: nat| #[trigger] spec.entails(p(n).leads_to(p(0))),
{
    let pre = {
        forall |n: nat| #![trigger p(n)] (n > 0 ==> spec.entails(p(n).leads_to(p((n - 1) as nat))))
    };
    assert forall |n: nat| pre implies #[trigger] spec.entails(p(n).leads_to(p(0))) by {
        leads_to_rank_step_one_help(spec, p, n);
    }
}

proof fn leads_to_rank_step_one_help<T>(spec: TempPred<T>, p: spec_fn(nat) -> TempPred<T>, n: nat)
    requires
        forall |n: nat| #![trigger p(n)] (n > 0 ==> spec.entails(p(n).leads_to(p((n - 1) as nat)))),
    ensures
        spec.entails(p(n).leads_to(p(0))),
    decreases n,
{
    if n > 0 {
        // p(n) ~> p(n - 1), p(n - 1) ~> p(0)
        // combine with leads-to transitivity
        leads_to_rank_step_one_help(spec, p, (n - 1) as nat);
        leads_to_trans_n!(spec, p(n), p((n - 1) as nat), p(0));
    } else {
        // p(0) ~> p(0) trivially
        leads_to_self_temp(p(0));
    }
}

// usize version of the proof rule leads_to_rank_step_one.
pub proof fn leads_to_rank_step_one_usize<T>(spec: TempPred<T>, p: spec_fn(usize) -> TempPred<T>)
    requires
        forall |n: usize| #![trigger p(n)] (n > 0 ==> spec.entails(p(n).leads_to(p((n - 1) as usize)))),
    ensures
        forall |n: usize| #[trigger] spec.entails(p(n).leads_to(p(0))),
{
    let pre = {
        forall |n: usize| #![trigger p(n)] (n > 0 ==> spec.entails(p(n).leads_to(p((n - 1) as usize))))
    };
    assert forall |n: usize| pre implies #[trigger] spec.entails(p(n).leads_to(p(0))) by {
        leads_to_rank_step_one_usize_help(spec, p, n);
    }
}

proof fn leads_to_rank_step_one_usize_help<T>(spec: TempPred<T>, p: spec_fn(usize) -> TempPred<T>, n: usize)
    requires
        forall |n: usize| #![trigger p(n)] (n > 0 ==> spec.entails(p(n).leads_to(p((n - 1) as usize)))),
    ensures
        spec.entails(p(n).leads_to(p(0))),
    decreases n,
{
    if n > 0 {
        // p(n) ~> p(n - 1), p(n - 1) ~> p(0)
        // combine with leads-to transitivity
        leads_to_rank_step_one_usize_help(spec, p, (n - 1) as usize);
        leads_to_trans_n!(spec, p(n), p((n - 1) as usize), p(0));
    } else {
        // p(0) ~> p(0) trivially
        leads_to_self_temp(p(0));
    }
}

// Proving p leads to q vacuously.
// pre:
//     spec |= []r
//     p /\ r == false
// post:
//     spec |= p ~> q
pub proof fn vacuous_leads_to<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(always(r)),
        p.and(r) == false_pred::<T>(),
    ensures
        spec.entails(p.leads_to(q)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(q).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(q).satisfied_by(ex.suffix(i)) by {
            assert_by(!p.satisfied_by(ex.suffix(i)), {
                implies_apply::<T>(ex, spec, always(r));
//                assert(r.satisfied_by(ex.suffix(i)));
                if p.satisfied_by(ex.suffix(i)) {
                    assert(p.and(r).satisfied_by(ex.suffix(i)));
//                    assert(p.and(r) != false_pred::<T>());
                }
            });
        }
    }
}

// Proving p leads to q by borrowing the inv.
// pre:
//     spec |= p /\ inv ~> q
//     spec |= []inv
// post:
//     spec |= p ~> q
pub proof fn leads_to_by_borrowing_inv<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, inv: TempPred<T>)
    requires
        spec.entails(p.and(inv).leads_to(q)),
        spec.entails(always(inv)),
    ensures
        spec.entails(p.leads_to(q)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(q).satisfied_by(ex) by {
        assert forall |i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(q).satisfied_by(ex.suffix(i)) by {
            instantiate_entailed_always(ex, i, spec, inv);
            instantiate_entailed_leads_to(ex, i, spec, p.and(inv), q);
        }
    }
}

}
