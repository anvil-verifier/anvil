use vstd::prelude::*;

verus! {

#[is_variant]
pub enum VDeploymentReconcileStep {
    Init,
    AfterGetReplicaSets,
    AfterGetPodMap,
    Done,
    ScaleReplicaSet(VReplicaSet, ScaleOperation),
    Error,
}

pub enum ScaleOperation {
    Up,
    Down,
}

impl std::marker::Copy for VDeploymentReconcileStep {}

impl std::clone::Clone for VDeploymentReconcileStep {
    fn clone(&self) -> (result: Self)
        ensures result == self
    { *self }
}

impl View for VReplicaSetReconcileStep {
    type V = VDeploymentReconcileStepView;

    open spec fn view(&self) -> VDeploymentReconcileStepView {
        match self {
            VDeploymentReconcileStep::Init => VDeploymentReconcileStepView::Init,
            VDeploymentReconcileStep::AfterGetReplicaSets => VDeploymentReconcileStepView::AfterGetReplicaSets,
            VDeploymentReconcileStep::AfterGetPodMap => VDeploymentReconcileStepView::AfterGetPodMap,
            VDeploymentReconcileStep::Done => VDeploymentReconcileStepView::Done,
            VDeploymentReconcileStep::ScaleReplicaSet(rs, operation) => ScaleReplicaSet(rs.view(), *operation as nat),
            VDeploymentReconcileStep::Error => VDeploymentReconcileStepView::Error,
        }
    }
}

#[is_variant]
pub enum VDeploymentReconcileStepView {
    Init,
    AfterGetReplicaSets,
    AfterGetPodMap,
    Done,
    ScaleReplicaSet(VReplicaSetView, nat),
    Error,
}

}