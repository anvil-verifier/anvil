use crate::kubernetes_api_objects::spec::prelude::*;
use crate::vdeployment_controller::{
    trusted::{step::*, spec_types::*},
    model::{install::*, reconciler::*},
};
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    //cluster::*, 
    //message::*
};
use vstd::prelude::*;

verus! {

pub open spec fn at_step(step: VDeploymentReconcileStepView) -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| VDeploymentReconcileState::unmarshal(s).unwrap().reconcile_step == step
}

pub open spec fn at_step_and_pred(step: VDeploymentReconcileStepView, pred: spec_fn(VDeploymentReconcileState) -> bool)
    -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| at_step(step)(s) && pred(VDeploymentReconcileState::unmarshal(s).unwrap())
}
}