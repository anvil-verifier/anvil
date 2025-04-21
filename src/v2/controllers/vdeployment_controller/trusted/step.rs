use vstd::prelude::*;

verus! {

pub enum VDeploymentReconcileStep {
    Init,
    AfterGetReplicaSets,
    RollReplicas,
    Done,
    Error,
}

impl std::marker::Copy for VDeploymentReconcileStep {}

impl std::clone::Clone for VDeploymentReconcileStep {
    fn clone(&self) -> (result: Self)
        ensures result == self
    { *self }
}

impl View for VDeploymentReconcileStep {
    type V = VDeploymentReconcileStepView;

    open spec fn view(&self) -> VDeploymentReconcileStepView {
        match self {
            VDeploymentReconcileStep::Init => VDeploymentReconcileStepView::Init,
            VDeploymentReconcileStep::AfterGetReplicaSets => VDeploymentReconcileStepView::AfterGetReplicaSets,
            VDeploymentReconcileStep::RollReplicas => VDeploymentReconcileStepView::RollReplicas,
            VDeploymentReconcileStep::Done => VDeploymentReconcileStepView::Done,
            VDeploymentReconcileStep::Error => VDeploymentReconcileStepView::Error,
        }
    }
}

#[is_variant]
pub enum VDeploymentReconcileStepView {
    Init,
    AfterGetReplicaSets,
    RollReplicas,
    Done,
    Error,
}

}