use crate::composition::vreplicaset_reconciler::*;
use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::proof::core::*;
use crate::kubernetes_cluster::spec::cluster::*;
use vstd::prelude::*;

verus! {

// Opaque id assignments for the controllers we intend to prove CORE for.
// New controllers should reserve a fresh id here.
pub open spec fn vrs_id() -> int { 1 }

// The CoreCluster used throughout composition proofs. Wraps a caller-supplied
// Cluster with the registry of all controllers whose CORE proofs exist.
pub open spec fn core_cluster(cluster: Cluster) -> CoreCluster {
    CoreCluster {
        cluster,
        registry: Map::empty().insert(vrs_id(), vrs_controller_spec(vrs_id())),
    }
}

}
