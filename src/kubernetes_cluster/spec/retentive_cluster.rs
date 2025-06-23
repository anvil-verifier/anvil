use crate::kubernetes_cluster::spec::{api_server::types::InstalledTypes, cluster::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

// ClusterHistory includes the current state and a sequence of past states.
pub struct ClusterHistory {
    pub current: ClusterState,
    pub past: Seq<ClusterState>,
}

pub struct RetentiveCluster {
    pub installed_types: InstalledTypes,
    pub controller_models: Map<int, ControllerModel>,
}

// RetentiveCluster is simply the original Cluster state machine and a history of the states.
// The history is initially empty and each step the previous state is pushed to the history.
impl RetentiveCluster {
    pub open spec fn init(self) -> StatePred<ClusterHistory> {
        |h: ClusterHistory| {
            &&& self.to_cluster().init()(h.current)
            &&& h.past == Seq::<ClusterState>::empty()
        }
    }

    pub open spec fn next(self) -> ActionPred<ClusterHistory> {
        |h: ClusterHistory, h_prime: ClusterHistory| {
            &&& self.to_cluster().next()(h.current, h_prime.current)
            &&& h_prime.past == h.past.push(h.current)
        }
    }

    #[verifier(inline)]
    pub open spec fn to_cluster(self) -> Cluster {
        Cluster {
            installed_types: self.installed_types,
            controller_models: self.controller_models,
        }
    }
}

}
