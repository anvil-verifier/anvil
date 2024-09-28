// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster_state_machine::*, retentive_cluster::*};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

impl RetentiveCluster {

// If an invariant (on the cluster state, not the history) holds for the state machine w/ the history
// then it holds for the state machine w/o the history.
//
// This allows us to prove some invariant using the history of the retentive state machine
// and then transfer it back to the original state machine.
pub proof fn transfer_invariant_to_cluster(self, spec: TempPred<ClusterState>, inv: StatePred<ClusterState>)
    requires
        lift_state(self.init()).and(always(lift_action(self.next()))).entails(always(lift_state(|h: ClusterHistory| inv(h.current)))),
        spec.entails(lift_state(self.to_cluster().init())),
        spec.entails(always(lift_action(self.to_cluster().next()))),
    ensures
        spec.entails(always(lift_state(inv))),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(lift_state(inv)).satisfied_by(ex) by {
        let ex_h = Execution::<ClusterHistory> {
            nat_to_state: |i: nat| Self::construct_history_from_state(i, ex)
        };
        assert(spec.implies(lift_state(self.to_cluster().init())).satisfied_by(ex));
        assert(spec.implies(always(lift_action(self.to_cluster().next()))).satisfied_by(ex));
        assert_by(lift_state(self.init()).satisfied_by(ex_h), {
            let s = ex.head();
            let h = ex_h.head();
            self.reverse_refinement_init(s, h);
        });
        assert_by(always(lift_action(self.next())).satisfied_by(ex_h), {
            assert forall |i| #[trigger] lift_action(self.next()).satisfied_by(ex_h.suffix(i)) by {
                assert(lift_action(self.to_cluster().next()).satisfied_by(ex.suffix(i)));
                let s = ex.suffix(i).head();
                let s_prime = ex.suffix(i).head_next();
                let h = ex_h.suffix(i).head();
                let h_prime = ex_h.suffix(i).head_next();
                self.reverse_refinement_next(s, s_prime, h, h_prime);
            }
        });
        assert_by(always(lift_state(|h: ClusterHistory| inv(h.current))).satisfied_by(ex_h), {
            assert(lift_state(self.init()).and(always(lift_action(self.next()))).implies(always(lift_state(|h: ClusterHistory| inv(h.current)))).satisfied_by(ex_h));
        });
        assert_by(always(lift_state(inv)).satisfied_by(ex), {
            assert forall |i| #[trigger] lift_state(inv).satisfied_by(ex.suffix(i)) by {
                assert(lift_state(|h: ClusterHistory| inv(h.current)).satisfied_by(ex_h.suffix(i)));
            }
        })
    }
}

// If an invariant holds for the state machine w/o the history
// then it holds for the state machine w/ the history.
//
// This allows us to use the invariants already proven in the original state machine
// when proving invariants in the retentive state machine.
pub proof fn transfer_invariant_from_cluster(self, spec: TempPred<ClusterHistory>, inv: StatePred<ClusterState>)
    requires
        lift_state(self.to_cluster().init()).and(always(lift_action(self.to_cluster().next()))).entails(always(lift_state(inv))),
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
    ensures
        spec.entails(always(lift_state(|h: ClusterHistory| inv(h.current)))),
{
    let inv_h = |h: ClusterHistory| inv(h.current);
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(lift_state(inv_h)).satisfied_by(ex) by {
        let ex_s = Execution::<ClusterState> {
            nat_to_state: |i: nat| (ex.nat_to_state)(i).current
        };
        assert(spec.implies(lift_state(self.init())).satisfied_by(ex));
        assert(spec.implies(always(lift_action(self.next()))).satisfied_by(ex));
        assert_by(lift_state(self.to_cluster().init()).satisfied_by(ex_s), {
            let h = ex.head();
            self.refinement_init(h);
        });
        assert_by(always(lift_action(self.to_cluster().next())).satisfied_by(ex_s), {
            assert forall |i| #[trigger] lift_action(self.to_cluster().next()).satisfied_by(ex_s.suffix(i)) by {
                assert(lift_action(self.next()).satisfied_by(ex.suffix(i)));
                let h = ex.suffix(i).head();
                let h_prime = ex.suffix(i).head_next();
                self.refinement_next(h, h_prime);
            }
        });
        assert_by(always(lift_state(inv)).satisfied_by(ex_s), {
            assert(lift_state(self.to_cluster().init()).and(always(lift_action(self.to_cluster().next()))).implies(always(lift_state(inv))).satisfied_by(ex_s));
        });
        assert_by(always(lift_state(inv_h)).satisfied_by(ex), {
            assert forall |i| #[trigger] lift_state(inv_h).satisfied_by(ex.suffix(i)) by {
                assert(lift_state(inv).satisfied_by(ex_s.suffix(i)));
            }
        })
    }
}

pub open spec fn construct_history_from_state(i: nat, ex: Execution<ClusterState>) -> ClusterHistory
    decreases i
{
    ClusterHistory {
        current: (ex.nat_to_state)(i),
        past: if i == 0 {
                Seq::<ClusterState>::empty()
            } else {
                Self::construct_history_from_state((i - 1) as nat, ex).past.push((ex.nat_to_state)((i - 1) as nat))
            },
    }
}

pub proof fn refinement_init(self, h: ClusterHistory)
    requires
        self.init()(h),
    ensures
        self.to_cluster().init()(h.current),
{}

pub proof fn refinement_next(self, h: ClusterHistory, h_prime: ClusterHistory)
    requires
        self.next()(h, h_prime),
    ensures
        self.to_cluster().next()(h.current, h_prime.current),
{}

pub proof fn reverse_refinement_init(self, s: ClusterState, h: ClusterHistory)
    requires
        self.to_cluster().init()(s),
        h.current == s,
        h.past == Seq::<ClusterState>::empty(),
    ensures
        self.init()(h),
{}

pub proof fn reverse_refinement_next(self, s: ClusterState, s_prime: ClusterState, h: ClusterHistory, h_prime: ClusterHistory)
    requires
        self.to_cluster().next()(s, s_prime),
        h.current == s,
        h_prime.current == s_prime,
        h_prime.past == h.past.push(s),
    ensures
        self.next()(h, h_prime),
{}

}



}
