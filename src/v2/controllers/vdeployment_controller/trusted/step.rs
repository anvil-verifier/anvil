use vstd::prelude::*;

verus! {

#[is_variant]
pub enum VDeploymentReconcileStep {
    Init,
    More,
    Done,
    Error,
}

impl std::marker::Copy for VDeploymentReconcileStep {}

impl std::clone::Clone for VDeploymentReconcileStep {
    fn clone(&self) -> (result: Self)
        ensures result == self
    { *self }
}

}
