// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::function::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

/// This lemmas is unfortunately necessary when using tla_forall.
pub proof fn use_tla_forall<T, A>(spec: TempPred<T>, a_to_temp_pred: FnSpec(A) -> TempPred<T>, a: A)
    requires
        spec.entails(tla_forall(a_to_temp_pred)),
    ensures
        spec.entails(a_to_temp_pred(a)),
{
    entails_apply_auto::<T>();
    assert forall |ex: Execution<T>| #[trigger] spec.implies(a_to_temp_pred(a)).satisfied_by(ex) by {
        assert(spec.implies(tla_forall(a_to_temp_pred)).satisfied_by(ex));
    };
}

proof fn execution_suffix_zero_merge<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        p.satisfied_by(ex.suffix(0)),
    ensures
        p.satisfied_by(ex),
{
    fun_ext::<nat, T>(ex.suffix(0).nat_to_state, ex.nat_to_state);
}

proof fn execution_suffix_zero_split<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        p.satisfied_by(ex),
    ensures
        p.satisfied_by(ex.suffix(0)),
{
    fun_ext::<nat, T>(ex.nat_to_state, ex.suffix(0).nat_to_state);
}

proof fn execution_suffix_merge<T>(ex: Execution<T>, p: TempPred<T>, i: nat, j: nat)
    requires
        p.satisfied_by(ex.suffix(i).suffix(j)),
    ensures
        p.satisfied_by(ex.suffix(i + j)),
{
    fun_ext::<nat, T>(ex.suffix(i).suffix(j).nat_to_state, ex.suffix(i + j).nat_to_state);
}

proof fn execution_suffix_split<T>(ex: Execution<T>, p: TempPred<T>, i: nat, j: nat)
    requires
        p.satisfied_by(ex.suffix(i + j)),
    ensures
        p.satisfied_by(ex.suffix(i).suffix(j)),
{
    fun_ext::<nat, T>(ex.suffix(i + j).nat_to_state, ex.suffix(i).suffix(j).nat_to_state);
}

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

proof fn implies_apply<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.implies(q).satisfied_by(ex),
        p.satisfied_by(ex),
    ensures
        q.satisfied_by(ex),
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

proof fn entails_trans<T>(p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
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
        execution_suffix_split::<T>(ex, p, i, j);
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
    execution_suffix_zero_merge::<T>(ex, p);
}

proof fn eventually_propagate_backwards<T>(ex: Execution<T>, p: TempPred<T>, i: nat)
    requires
        eventually(p).satisfied_by(ex.suffix(i)),
    ensures
        eventually(p).satisfied_by(ex),
{
    eventually_unfold::<T>(ex.suffix(i), p);
    let witness_idx = eventually_choose_witness(ex.suffix(i), p);
    execution_suffix_merge::<T>(ex, p, i, witness_idx);
}

proof fn eventually_proved_by_witness<T>(ex: Execution<T>, p: TempPred<T>, witness_idx: nat)
    requires
        p.satisfied_by(ex.suffix(witness_idx)),
    ensures
        eventually(p).satisfied_by(ex)
{}

spec fn eventually_choose_witness<T>(ex: Execution<T>, p: TempPred<T>) -> nat
    recommends
        exists |i: nat| p.satisfied_by(#[trigger] ex.suffix(i)),
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

proof fn implies_to_leads_to<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
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
            execution_suffix_zero_split(ex.suffix(i), q);
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
        execution_suffix_zero_merge(ex, p);
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
        execution_suffix_zero_split::<T>(ex, p);
        assert(p.satisfied_by(ex.suffix(0)));
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
                execution_suffix_merge::<T>(ex.suffix(i), p, idx, 1);
            } else {
                later_unfold::<T>(ex.suffix(i).suffix(idx), q);
                execution_suffix_merge::<T>(ex.suffix(i), q, idx, 1);
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

proof fn next_preserves_inv_assume_rec<T>(ex: Execution<T>, next: ActionPred<T>, asm: StatePred<T>, inv: StatePred<T>, i: nat)
    requires
        inv(ex.head()),
        forall |idx: nat| next(#[trigger] ex.suffix(idx).head(), ex.suffix(idx).head_next()),
        forall |idx: nat| asm(#[trigger] ex.suffix(idx).head()),
        forall |idx: nat| inv(#[trigger] ex.suffix(idx).head()) && next(ex.suffix(idx).head(), ex.suffix(idx).head_next()) && asm(ex.suffix(idx).head())
            ==> inv(ex.suffix(idx).head_next()),
    ensures
        inv(ex.suffix(i).head()),
    decreases
        i,
{
    if i == 0 {
        assert(inv(ex.suffix(0).head()));
    } else {
        next_preserves_inv_assume_rec::<T>(ex, next, asm, inv, (i-1) as nat);
    }
}

/// Get the initial always by induction.
/// pre:
///     |= init => inv
///     |= inv /\ next => inv'
///     spec |= init /\ []next
/// post:
///     spec |= []inv
pub proof fn init_invariant<T>(spec: TempPred<T>, init: StatePred<T>, next: ActionPred<T>, inv: StatePred<T>)
    requires
        forall |s: T| state_pred_call(init, s) ==> inv(s),
        forall |s, s_prime: T| inv(s) && action_pred_call(next, s, s_prime) ==> inv(s_prime),
        spec.entails(lift_state(init).and(always(lift_action(next)))),
    ensures
        spec.entails(always(lift_state(inv))),
{
    assert forall |ex: Execution<T>| spec.satisfied_by(ex)
    implies #[trigger] always(lift_state(inv)).satisfied_by(ex) by {
        entails_apply(ex, spec, lift_state(init).and(always(lift_action(next))));
        always_unfold::<T>(ex, lift_action(next));
        assert forall |i: nat| inv(#[trigger] ex.suffix(i).head()) by {
            assert forall |idx: nat| init(#[trigger] ex.suffix(idx).head()) implies inv(ex.suffix(idx).head()) by {
                assert(state_pred_call(init, ex.suffix(idx).head()));
            };
            init_invariant_rec(ex, init, next, inv, i);
        };
    };
}

/// Get the initial leads_to.
/// pre:
///     |= p /\ next => p' /\ q'
///     |= p /\ next /\ forward => q'
///     spec |= []next
///     spec |= []p ~> forward
/// post:
///     spec |= p ~> q
pub proof fn leads_to_by_forward_temp<T>(spec: TempPred<T>, next: TempPred<T>, forward: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
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
                execution_suffix_merge::<T>(ex.suffix(i), q, witness_idx, 1);

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
pub proof fn leads_to_by_forward_assume_temp<T>(spec: TempPred<T>, next: TempPred<T>, forward: TempPred<T>, asm: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(p.and(next).and(asm).implies(later(p).or(later(q))))),
        spec.entails(always(p.and(next).and(forward).implies(later(q)))),
        spec.entails(always(next)),
        spec.entails(always(p).leads_to(forward)),
    ensures
        spec.entails(p.and(always(asm)).leads_to(q)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(p.and(always(asm))).leads_to(forward).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, always(p).leads_to(forward));
        leads_to_unfold::<T>(ex, always(p), forward);
        assert forall |i| #[trigger] always(p.and(always(asm))).satisfied_by(ex.suffix(i))
        implies eventually(forward).satisfied_by(ex.suffix(i)) by {
            always_unfold::<T>(ex.suffix(i), p.and(always(asm)));
            implies_apply::<T>(ex.suffix(i), always(p), eventually(forward));
        };
    };

    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(p.and(always(asm)).and(next).implies(later(p.and(always(asm))).or(later(q)))).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, always(p.and(next).and(asm).implies(later(p).or(later(q)))));
        assert forall |i| #[trigger] p.and(always(asm)).and(next).satisfied_by(ex.suffix(i))
        implies later(p.and(always(asm))).or(later(q)).satisfied_by(ex.suffix(i)) by {
            always_unfold::<T>(ex.suffix(i), asm);
            execution_suffix_zero_merge::<T>(ex.suffix(i), asm);
            implies_apply::<T>(ex.suffix(i), p.and(next).and(asm), later(p).or(later(q)));
            always_propagate_forwards::<T>(ex.suffix(i), asm, 1);
        };
    };

    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(p.and(always(asm)).and(next).and(forward).implies(later(q))).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, always(p.and(next).and(forward).implies(later(q))));
        assert forall |i| #[trigger] p.and(always(asm)).and(next).and(forward).satisfied_by(ex.suffix(i))
        implies later(q).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex.suffix(i), p.and(next).and(forward), later(q));
        };
    };

    leads_to_by_forward_temp::<T>(spec, next, forward, p.and(always(asm)), q);
}

/// Get the initial leads_to with a stronger wf assumption than leads_to_by_forward.
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
        forall |s, s_prime: T| p(s) && action_pred_call(next, s, s_prime) ==> p(s_prime) || q(s_prime),
        forall |s, s_prime: T| p(s) && action_pred_call(next, s, s_prime) && forward(s, s_prime) ==> q(s_prime),
        forall |s: T| state_pred_call(p, s) ==> enabled(forward)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(weak_fairness(forward)),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(lift_state(p)).leads_to(lift_action(forward)).satisfied_by(ex) by {
        assert forall |i| #[trigger] always(lift_state(p)).satisfied_by(ex.suffix(i)) implies eventually(lift_action(forward)).satisfied_by(ex.suffix(i)) by {
            assert(always(lift_state(p).implies(lift_state(enabled(forward)))).satisfied_by(ex.suffix(i)));
            implies_apply_with_always::<T>(ex.suffix(i), lift_state(p), lift_state(enabled(forward)));
            execution_suffix_merge::<T>(ex, lift_state(enabled(forward)), i, 0);

            implies_apply::<T>(ex, spec, weak_fairness(forward));
            weak_fairness_unfold::<T>(ex, forward);
            implies_apply::<T>(ex.suffix(i), lift_state(enabled(forward)), eventually(lift_action(forward)));
        };
    };
    leads_to_by_forward_temp::<T>(spec, lift_action(next), lift_action(forward), lift_state(p), lift_state(q));
}

/// Get the initial leads_to by assuming (1) always asm and (2) a stronger wf assumption than leads_to_by_forward_assume.
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
        forall |s, s_prime: T| p(s) && action_pred_call(next, s, s_prime) && asm(s) ==> p(s_prime) || q(s_prime),
        forall |s, s_prime: T| p(s) && action_pred_call(next, s, s_prime) && forward(s, s_prime) ==> q(s_prime),
        forall |s: T| state_pred_call(p, s) ==> enabled(forward)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(weak_fairness(forward)),
    ensures
        spec.entails(lift_state(p).and(always(lift_state(asm))).leads_to(lift_state(q))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(lift_state(p)).leads_to(lift_action(forward)).satisfied_by(ex) by {
        assert forall |i| #[trigger] always(lift_state(p)).satisfied_by(ex.suffix(i)) implies eventually(lift_action(forward)).satisfied_by(ex.suffix(i)) by {
            assert(always(lift_state(p).implies(lift_state(enabled(forward)))).satisfied_by(ex.suffix(i)));
            implies_apply_with_always::<T>(ex.suffix(i), lift_state(p), lift_state(enabled(forward)));
            execution_suffix_merge::<T>(ex, lift_state(enabled(forward)), i, 0);

            implies_apply::<T>(ex, spec, weak_fairness(forward));
            weak_fairness_unfold::<T>(ex, forward);
            implies_apply::<T>(ex.suffix(i), lift_state(enabled(forward)), eventually(lift_action(forward)));
        };
    };
    leads_to_by_forward_assume_temp::<T>(spec, lift_action(next), lift_action(forward), lift_state(asm), lift_state(p), lift_state(q));
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
///     |= p1 => p2
///     |= q1 => q2
/// post:
///     |= p1 /\ q1 => p2 /\ q2
pub proof fn implies_preserved_by_and_temp<T>(p1: TempPred<T>, p2: TempPred<T>, q1: TempPred<T>, q2: TempPred<T>)
    requires
        valid(p1.implies(p2)),
        valid(q1.implies(q2)),
    ensures
        valid(p1.and(q1).implies(p2.and(q2))),
{
    assert forall |ex| p1.and(q1).satisfied_by(ex) implies p2.and(q2).satisfied_by(ex) by {
        implies_apply::<T>(ex, p1, p2);
        implies_apply::<T>(ex, q1, q2);
    };
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

/// Introduce always to both sides of equals.
/// pre:
///     |= p <=> q
/// post:
///     |= []p <=> []q
pub proof fn eq_preserved_by_always_temp<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        valid(p.equals(q)),
    ensures
        valid(always(p).equals(always(q))),
{
    valid_equals_to_valid_implies::<T>(p, q);
    implies_preserved_by_always_temp::<T>(p, q);
    implies_preserved_by_always_temp::<T>(q, p);
    valid_implies_to_valid_equals::<T>(always(p), always(q));
}

/// StatePred version of eq_preserved_by_always_temp.
pub proof fn eq_preserved_by_always<T>(p: StatePred<T>, q: StatePred<T>)
    requires
        valid(lift_state(p).equals(lift_state(q))),
    ensures
        valid(always(lift_state(p)).equals(always(lift_state(q)))),
{
    eq_preserved_by_always_temp::<T>(lift_state(p), lift_state(q))
}

/// Auto version of eq_preserved_by_always_temp.
pub proof fn eq_preserved_by_always_auto<T>()
    ensures
        forall |p: TempPred<T>, q: TempPred<T>|
        #![trigger always(p), always(q)]
        valid(p.equals(q)) ==> valid(always(p).equals(always(q))),
{
    assert forall |p: TempPred<T>, q: TempPred<T>| #[trigger] valid(p.equals(q))
    implies valid(always(p).equals(always(q))) by {
        eq_preserved_by_always_temp::<T>(p, q);
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

/// Get another always by equals.
/// pre:
///     |= p <=> q
///     spec |= []p
/// post:
///     spec |= []q
pub proof fn always_eq_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        valid(p.equals(q)),
        spec.entails(always(p)),
    ensures
        spec.entails(always(q)),
{
    eq_preserved_by_always_temp::<T>(p, q);
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(q).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, always(p));
        equals_apply::<T>(ex, always(p), always(q));
    };
}

/// StatePred version of always_eq_temp.
pub proof fn always_eq<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        valid(lift_state(p).equals(lift_state(q))),
        spec.entails(always(lift_state(p))),
    ensures
        spec.entails(always(lift_state(q))),
{
    always_eq_temp::<T>(spec, lift_state(p), lift_state(q));
}

/// Auto version of always_eq_temp.
pub proof fn always_eq_auto<T>(spec: TempPred<T>)
    ensures
        forall |p: TempPred<T>, q: TempPred<T>| valid(p.equals(q)) && spec.entails(#[trigger] always(p))
        ==> spec.entails(#[trigger] always(q)),
{
    assert forall |p: TempPred<T>, q: TempPred<T>| valid(p.equals(q)) && spec.entails(#[trigger] always(p))
    implies spec.entails(#[trigger] always(q)) by {
        always_eq_temp::<T>(spec, p, q);
    }
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
                execution_suffix_split::<T>(ex, p.implies(q), i, j);

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

/// Introduce eventually to both sides of equals.
/// pre:
///     |= p <=> q
/// post:
///     |= <>p <=> <>q
pub proof fn eq_preserved_by_eventually_temp<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        valid(p.equals(q)),
    ensures
        valid(eventually(p).equals(eventually(q))),
{
    valid_equals_to_valid_implies::<T>(p, q);
    implies_preserved_by_eventually_temp::<T>(p, q);
    implies_preserved_by_eventually_temp::<T>(q, p);
    valid_implies_to_valid_equals::<T>(eventually(p), eventually(q));
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

/// Get another eventually by equals.
/// pre:
///     |= p <=> q
///     spec |= <>p
/// post:
///     spec |= <>q
pub proof fn eventually_eq_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        valid(p.equals(q)),
        spec.entails(eventually(p)),
    ensures
        spec.entails(eventually(q)),
{
    eq_preserved_by_eventually_temp::<T>(p, q);
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies eventually(q).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, eventually(p));
        equals_apply::<T>(ex, eventually(p), eventually(q));
    };
}

/// StatePred version of eventually_eq_temp.
pub proof fn eventually_eq<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        valid(lift_state(p).equals(lift_state(q))),
        spec.entails(eventually(lift_state(p))),
    ensures
        spec.entails(eventually(lift_state(q))),
{
    eventually_eq_temp::<T>(spec, lift_state(p), lift_state(q));
}

/// Auto version of eventually_eq_temp.
pub proof fn eventually_eq_auto<T>(spec: TempPred<T>)
    ensures
        forall |p: TempPred<T>, q: TempPred<T>|
            valid(p.equals(q)) && spec.entails(#[trigger] eventually(p))
            ==> spec.entails(#[trigger] eventually(q)),
{
    assert forall |p: TempPred<T>, q: TempPred<T>|
    valid(p.equals(q)) && spec.entails(#[trigger] eventually(p))
    implies spec.entails(#[trigger] eventually(q)) by {
        eventually_eq_temp(spec, p, q);
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
        execution_suffix_zero_merge::<T>(ex, p.implies(eventually(q)));
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
            execution_suffix_merge(ex, q, i, q_witness_idx);

            entails_apply(ex, spec, q.leads_to(r));
            always_unfold(ex, q.implies(eventually(r)));
            implies_apply(ex.suffix(i + q_witness_idx), q, eventually(r));
            execution_suffix_split(ex, eventually(r), i, q_witness_idx);

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

/// Lite version of leads_to_weaken_auto.
pub proof fn leads_to_weaken_lite_auto<T>(spec: TempPred<T>)
    ensures
        forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
            valid(p2.implies(p1)) && valid(q1.implies(q2)) && spec.entails(#[trigger] p1.leads_to(q1))
            ==> spec.entails(#[trigger] p2.leads_to(q2))
{
    assert forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
    valid(p2.implies(p1)) && valid(q1.implies(q2)) && spec.entails(#[trigger] p1.leads_to(q1))
    implies spec.entails(#[trigger] p2.leads_to(q2)) by {
        leads_to_weaken_temp(spec, p1, q1, p2, q2);
    };
}

/// Weaken another leads_to by equals.
/// pre:
///     |= p2 <=> p1
///     |= q1 <=> q2
///     spec |= p1 ~> q1
/// post:
///     spec |= p2 ~> q2
proof fn leads_to_eq_temp<T>(spec: TempPred<T>, p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>)
    requires
        valid(p2.equals(p1)),
        valid(q1.equals(q2)),
        spec.entails(p1.leads_to(q1)),
    ensures
        spec.entails(p2.leads_to(q2)),
{
    valid_equals_to_valid_implies::<T>(p2, p1);
    valid_equals_to_valid_implies::<T>(q1, q2);
    implies_to_leads_to::<T>(spec, p2, p1);
    implies_to_leads_to::<T>(spec, q1, q2);
    leads_to_trans_temp::<T>(spec, p2, p1, q1);
    leads_to_trans_temp::<T>(spec, p2, q1, q2);
}

/// StatePred version of leads_to_eq_temp.
proof fn leads_to_eq<T>(spec: TempPred<T>, p1: StatePred<T>, q1: StatePred<T>, p2: StatePred<T>, q2: StatePred<T>)
    requires
        valid(lift_state(p2).equals(lift_state(p1))),
        valid(lift_state(q1).equals(lift_state(q2))),
        spec.entails(lift_state(p1).leads_to(lift_state(q1))),
    ensures
        spec.entails(lift_state(p2).leads_to(lift_state(q2))),
{
    leads_to_eq_temp::<T>(spec, lift_state(p1), lift_state(q1), lift_state(p2), lift_state(q2));
}

/// Auto version of leads_to_eq_temp.
pub proof fn leads_to_eq_auto<T>(spec: TempPred<T>)
    ensures
        forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
            valid(p2.equals(p1)) && valid(q1.equals(q2)) && spec.entails(#[trigger] p1.leads_to(q1))
            ==> spec.entails(#[trigger] p2.leads_to(q2))
{
    assert forall |p1: TempPred<T>, q1: TempPred<T>, p2: TempPred<T>, q2: TempPred<T>|
    valid(p2.equals(p1)) && valid(q1.equals(q2)) && spec.entails(#[trigger] p1.leads_to(q1))
    implies spec.entails(#[trigger] p2.leads_to(q2)) by {
        leads_to_eq_temp(spec, p1, q1, p2, q2);
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
                execution_suffix_zero_split::<T>(ex.suffix(i), q);
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
                execution_suffix_merge::<T>(ex.suffix(i), always(q), witness_q_idx, (witness_r_idx - witness_q_idx) as nat);
                eventually_proved_by_witness(ex.suffix(i), always(q.and(r)), witness_r_idx);
            } else {
                always_propagate_forwards::<T>(ex.suffix(i).suffix(witness_r_idx), r, (witness_q_idx - witness_r_idx) as nat);
                execution_suffix_merge::<T>(ex.suffix(i), always(r), witness_r_idx, (witness_q_idx - witness_r_idx) as nat);
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
    implies_preserved_by_and_temp::<T>(always(q), q, always(r), always(r));
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

/// Get leads_to always by assuming always asm.
/// pre:
///     |= q /\ next /\ asm => q
///     spec |= []next
///     spec |= p ~> q
/// post:
///     spec |= p /\ []asm ~> []q
pub proof fn leads_to_stable_assume<T>(spec: TempPred<T>, next: ActionPred<T>, asm: StatePred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        forall |s, s_prime: T| q(s) && action_pred_call(next, s, s_prime) && asm(s) ==> q(s_prime),
        spec.entails(always(lift_action(next))),
        spec.entails(lift_state(p).leads_to(lift_state(q))),
    ensures
        spec.entails(lift_state(p).and(always(lift_state(asm))).leads_to(always(lift_state(q)))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies lift_state(p).and(always(lift_state(asm))).leads_to(always(lift_state(q))).satisfied_by(ex) by {
        assert forall |i| #[trigger] lift_state(p).and(always(lift_state(asm))).satisfied_by(ex.suffix(i)) implies eventually(always(lift_state(q))).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, lift_state(p).leads_to(lift_state(q)));
            always_unfold::<T>(ex, lift_state(p).implies(eventually(lift_state(q))));
            implies_apply::<T>(ex.suffix(i), lift_state(p), eventually(lift_state(q)));
            let witness_idx = eventually_choose_witness::<T>(ex.suffix(i), lift_state(q));

            implies_apply::<T>(ex, spec, always(lift_action(next)));
            always_propagate_forwards::<T>(ex, lift_action(next), i);
            always_propagate_forwards::<T>(ex.suffix(i), lift_action(next), witness_idx);
            always_lift_action_unfold::<T>(ex.suffix(i).suffix(witness_idx), next);

            always_propagate_forwards::<T>(ex.suffix(i), lift_state(asm), witness_idx);
            always_lift_state_unfold::<T>(ex.suffix(i).suffix(witness_idx), asm);

            assert forall |j| #[trigger] lift_state(q).satisfied_by(ex.suffix(i).suffix(witness_idx).suffix(j)) by {
                assert forall |idx| q(#[trigger] ex.suffix(i).suffix(witness_idx).suffix(idx).head())
                && next(ex.suffix(i).suffix(witness_idx).suffix(idx).head(), ex.suffix(i).suffix(witness_idx).suffix(idx).head_next())
                && asm(ex.suffix(i).suffix(witness_idx).suffix(idx).head())
                implies q(ex.suffix(i).suffix(witness_idx).suffix(idx).head_next()) by {
                    assert(action_pred_call(next, ex.suffix(i).suffix(witness_idx).suffix(idx).head(), ex.suffix(i).suffix(witness_idx).suffix(idx).head_next()));
                };
                next_preserves_inv_assume_rec::<T>(ex.suffix(i).suffix(witness_idx), next, asm, q, j);
            };

            eventually_proved_by_witness::<T>(ex.suffix(i), always(lift_state(q)), witness_idx);
        };
    };
}

/// Get leads_to always by assuming always p.
/// pre:
///     |= q /\ next /\ asm => q
///     spec |= []next
///     spec |= []([]p => []asm)
///     spec |= p ~> q
/// post:
///     spec |= []p ~> []q
pub proof fn leads_to_stable_assume_p<T>(spec: TempPred<T>, next: ActionPred<T>, asm: StatePred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        forall |s, s_prime: T| q(s) && action_pred_call(next, s, s_prime) && asm(s) ==> q(s_prime),
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

/// Get leads_to always if q is preserved by next.
/// pre:
///     |= q /\ next => q'
///     spec |= []next
///     spec |= p ~> q
/// post:
///     spec |= p ~> []q
pub proof fn leads_to_stable<T>(spec: TempPred<T>, next: ActionPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        forall |s, s_prime: T| q(s) && action_pred_call(next, s, s_prime) ==> q(s_prime),
        spec.entails(always(lift_action(next))),
        spec.entails(lift_state(p).leads_to(lift_state(q))),
    ensures
        spec.entails(lift_state(p).leads_to(always(lift_state(q)))),
{
    let trivial = |s| true;
    leads_to_stable_assume::<T>(spec, next, trivial, p, q);

    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies lift_state(p).leads_to(always(lift_state(q))).satisfied_by(ex) by {
        assert forall |i| #[trigger] lift_state(p).satisfied_by(ex.suffix(i)) implies eventually(always(lift_state(q))).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, lift_state(p).and(always(lift_state(trivial))).leads_to(always(lift_state(q))));
            always_unfold::<T>(ex, lift_state(p).and(always(lift_state(trivial))).implies(eventually(always(lift_state(q)))));
        };
    };
}

/// Combination of leads_to_stable_assume_p and leads_to_always_combine_temp.
pub proof fn leads_to_stable_assume_p_combine<T>(spec: TempPred<T>, next: ActionPred<T>, asm: StatePred<T>, p: StatePred<T>, q: StatePred<T>, r: StatePred<T>)
    requires
        forall |s, s_prime: T| q(s) && #[trigger] action_pred_call(next, s, s_prime) && asm(s) ==> q(s_prime),
        forall |s, s_prime: T| r(s) && #[trigger] action_pred_call(next, s, s_prime) && asm(s) ==> r(s_prime),
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
        forall |s, s_prime: T| q(s) && action_pred_call(next, s, s_prime) ==> q(s_prime),
        forall |s, s_prime: T| r(s) && action_pred_call(next, s, s_prime) ==> r(s_prime),
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
                execution_suffix_split::<T>(ex, p.implies(eventually(q)), i, j);

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
