use vstd::prelude::*;

verus! {

pub enum VDeploymentReconcileStep {
    Init,
    AfterListVRS,
    AfterCreateNewVRS,
    AfterScaleNewVRS,
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
            VDeploymentReconcileStep::Done => VDeploymentReconcileStepView::Done,
            VDeploymentReconcileStep::Error => VDeploymentReconcileStepView::Error,
        }
    }
}

#[is_variant]
#[derive(PartialEq)]
pub enum VDeploymentReconcileStepView {
    Init,
    AfterListVRS,
    AfterCreateNewVRS,
    AfterScaleNewVRS,
    AfterScaleDownOldVRS,
    Done,
    Error,
}

// hacky workaround for
// The verifier does not yet support the following Rust feature: ==/!= for non smt equality types:
// (The type is not available in log, I hacked verus)
// Datatype(Path(Path(Some("v2_vdeployment_controller"), ["vdeployment_controller" :: "trusted" :: "step" :: "VDeploymentReconcileStepView"])), [], [])
impl VDeploymentReconcileStepView {
    pub open spec fn eq_step(self, other: VDeploymentReconcileStepView) -> bool {
        self == other
    }
}

}