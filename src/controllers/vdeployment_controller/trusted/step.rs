use vstd::prelude::*;

verus! {

pub enum VDeploymentReconcileStep {
    Init,
    AfterListVRS,
    AfterCreateNewVRS,
    AfterScaleNewVRS,
    AfterEnsureNewVRS,
    AfterScaleDownOldVRS,
    Done,
    Error,
}

// state machine of rolling update:
// init -- list vrs -> AfterListVRS
// AfterListVRS --> RollReplicas
// AfterListVRS -- create new vrs -> AfterCreateNewVRS
// AfterCreateNewVRS -- scale new vrs -> AfterScaleNewVRS
// AfterScaleNewVRS -- scale down old vrs -> AfterScaleDownOldVRS
// AfterScaleDownOldVRS -- scale down old vrs -> AfterScaleDownOldVRS
// AfterScaleDownOldVRS -- scale down old vrs -> Done

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
            VDeploymentReconcileStep::AfterListVRS => VDeploymentReconcileStepView::AfterListVRS,
            VDeploymentReconcileStep::AfterCreateNewVRS => VDeploymentReconcileStepView::AfterCreateNewVRS,
            VDeploymentReconcileStep::AfterScaleNewVRS => VDeploymentReconcileStepView::AfterScaleNewVRS,
            VDeploymentReconcileStep::AfterScaleDownOldVRS => VDeploymentReconcileStepView::AfterScaleDownOldVRS,
            VDeploymentReconcileStep::AfterEnsureNewVRS => VDeploymentReconcileStepView::AfterEnsureNewVRS,
            VDeploymentReconcileStep::Done => VDeploymentReconcileStepView::Done,
            VDeploymentReconcileStep::Error => VDeploymentReconcileStepView::Error,
        }
    }
}

pub enum VDeploymentReconcileStepView {
    Init,
    AfterListVRS,
    AfterCreateNewVRS,
    AfterScaleNewVRS,
    AfterEnsureNewVRS,
    AfterScaleDownOldVRS,
    Done,
    Error,
}

// eq_step is the tricky workaround for error:
// The verifier does not yet support the following Rust feature: ==/!= for non smt equality types:
// (The type is not available in log, I hacked verus)
// Datatype(Path(Path(Some("vdeployment_controller"), ["vdeployment_controller" :: "trusted" :: "step" :: "VDeploymentReconcileStepView"])), [], [])
impl VDeploymentReconcileStepView {
    pub open spec fn eq_step(self, other: VDeploymentReconcileStepView) -> bool {
        self == other
    }
}

}