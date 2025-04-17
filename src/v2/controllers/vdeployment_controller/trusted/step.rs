use vstd::prelude::*;
use crate::vreplicaset_controller::trusted::{spec_types::VReplicaSetView, exec_types::VReplicaSet};

verus! {

pub enum VDeploymentReconcileStep {
    Init,
    AfterGetReplicaSets,
    AfterGetPods,
    ScaleReplicaSet(VReplicaSet, int),
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
            VDeploymentReconcileStep::AfterGetPods => VDeploymentReconcileStepView::AfterGetPods,
            VDeploymentReconcileStep::Done => VDeploymentReconcileStepView::Done,
            VDeploymentReconcileStep::ScaleReplicaSet(rs, i) => VDeploymentReconcileStepView::ScaleReplicaSet(rs.view(), i),
            VDeploymentReconcileStep::Error => VDeploymentReconcileStepView::Error,
        }
    }
}

#[is_variant]
pub enum VDeploymentReconcileStepView {
    Init,
    AfterGetReplicaSets,
    AfterGetPods,
    Done,
    ScaleReplicaSet(VReplicaSetView, int),
    Error,
}

}