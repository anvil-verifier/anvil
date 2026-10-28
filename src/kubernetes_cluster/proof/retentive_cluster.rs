use crate::kubernetes_cluster::spec::{cluster::*, retentive_cluster::*};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

broadcast use verus_temporal_logic::rules::group_tla_rules;

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
    history_variable_preserves_invariant(
        spec, self.to_cluster().init(), self.to_cluster().next(), inv,
        |h: ClusterHistory| h.current,
        |s: ClusterState| ClusterHistory { current: s, past: Seq::<ClusterState>::empty() },
        |h: ClusterHistory, s_prime: ClusterState| ClusterHistory { current: s_prime, past: h.past.push(h.current) },
        self.init(), self.next(), |h: ClusterHistory| inv(h.current)
    );
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
    refinement_mapping_preserves_invariant(
        spec, self.init(), self.next(), |h: ClusterHistory| inv(h.current),
        |h: ClusterHistory| h.current, self.to_cluster().init(), self.to_cluster().next(), inv
    );
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
