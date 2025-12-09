use vstd::prelude::*;

verus! {

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

impl View for VReplicaSetReconcileStep {
    type V = VReplicaSetRecStepView;

    open spec fn view(&self) -> VReplicaSetRecStepView {
        match self {
            VReplicaSetReconcileStep::Init => VReplicaSetRecStepView::Init,
            VReplicaSetReconcileStep::AfterListPods => VReplicaSetRecStepView::AfterListPods,
            VReplicaSetReconcileStep::AfterCreatePod(diff) => VReplicaSetRecStepView::AfterCreatePod(*diff as nat),
            VReplicaSetReconcileStep::AfterDeletePod(diff) => VReplicaSetRecStepView::AfterDeletePod(*diff as nat),
            VReplicaSetReconcileStep::Done => VReplicaSetRecStepView::Done,
            VReplicaSetReconcileStep::Error => VReplicaSetRecStepView::Error,
        }
    }
}

pub enum VReplicaSetRecStepView {
    Init,
    AfterListPods,
    AfterCreatePod(nat),
    AfterDeletePod(nat),
    Done,
    Error,
}

}
