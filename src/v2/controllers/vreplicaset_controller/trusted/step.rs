use vstd::prelude::*;

verus! {

#[is_variant]
pub enum VReplicaSetReconcileStep {
    Init,
    AfterListPods,
    AfterCreatePod(usize),
    AfterDeletePod(usize),
    Done,
    Error,
}

impl std::marker::Copy for VReplicaSetReconcileStep {}

impl std::clone::Clone for VReplicaSetReconcileStep {
    fn clone(&self) -> (result: Self)
        ensures result == self
    { *self }
}

}
