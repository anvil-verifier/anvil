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

pub open spec fn at_step_closure(step: VDeploymentReconcileStepView) -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| VDeploymentReconcileState::unmarshal(s).unwrap().reconcile_step == step
}

pub open spec fn at_step_and_closure(step: VDeploymentReconcileStepView, pred: spec_fn(VDeploymentReconcileState) -> bool)
    -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| {
        let unmarshalled_s = VDeploymentReconcileState::unmarshal(s).unwrap();
        unmarshalled_s.reconcile_step == step && pred(unmarshalled_s)
    }
}

}