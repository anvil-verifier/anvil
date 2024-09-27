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
pub proof fn transfer_invariant_to_cluster(self, inv: StatePred<ClusterState>)
    requires
        forall |h| #[trigger] self.init()(h) ==> inv(h.current),
        forall |h: ClusterHistory, h_prime: ClusterHistory| inv(h.current) && #[trigger] self.next()(h, h_prime) ==> inv(h_prime.current),
    ensures
        forall |s| #[trigger] self.to_cluster().init()(s) ==> inv(s),
        forall |s, s_prime| inv(s) && #[trigger] self.to_cluster().next()(s, s_prime) ==> inv(s_prime),
{
    assert forall |s| #[trigger] self.to_cluster().init()(s) implies inv(s) by {
        let h = ClusterHistory {
            current: s,
            past: Seq::<ClusterState>::empty(),
        };
        self.reverse_refinement_init(s, h);
    }
    assert forall |s, s_prime| inv(s) && #[trigger] self.to_cluster().next()(s, s_prime) implies inv(s_prime) by {
        let h = ClusterHistory {
            current: s,
            past: arbitrary(),
        };
        let h_prime = ClusterHistory {
            current: s_prime,
            past: h.past.push(s),
        };
        self.reverse_refinement_next(s, s_prime, h, h_prime);
    }
}

// If an invariant holds for the state machine w/o the history
// then it holds for the state machine w/ the history.
//
// This allows us to use the invariants already proven in the original state machine
// when proving invariants in the retentive state machine.
pub proof fn transfer_invariant_from_cluster(self, inv: StatePred<ClusterState>)
    requires
        forall |s| #[trigger] self.to_cluster().init()(s) ==> inv(s),
        forall |s, s_prime| inv(s) && #[trigger] self.to_cluster().next()(s, s_prime) ==> inv(s_prime),
    ensures
        forall |h| #[trigger] self.init()(h) ==> inv(h.current),
        forall |h: ClusterHistory, h_prime: ClusterHistory| inv(h.current) && #[trigger] self.next()(h, h_prime) ==> inv(h_prime.current),

{
    assert forall |h| #[trigger] self.init()(h) implies inv(h.current) by {
        self.refinement_init(h);
    }
    assert forall |h: ClusterHistory, h_prime: ClusterHistory| inv(h.current) && #[trigger] self.next()(h, h_prime) implies inv(h_prime.current) by {
        self.refinement_next(h, h_prime);
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
