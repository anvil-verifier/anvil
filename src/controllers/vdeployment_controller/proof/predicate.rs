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
use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_cluster::spec::cluster::*;
use vstd::prelude::*;

verus! {

#[macro_export]
macro_rules! at_step_internal_or {
    ($vds:expr, ($step:expr, $pred:expr)) => {
        $vds.reconcile_step.eq_step($step) && $pred($vds)
    };

    // eq_step is the tricky workaround for error, see src/controllers/vdeployment_controller/trusted/step.rs
    ($vds:expr, $step:expr) => {
        $vds.reconcile_step.eq_step($step)
    };

    ($vds:expr, $head:tt, $($tail:tt)+) => {
        at_step_internal_or!($vds, $head) || at_step_internal_or!($vds, $($tail)+)
    };
}

// usage: at_step![step,*]
// step_or_pred = step | (step, pred)
#[macro_export]
macro_rules! at_step_or {
    [ $($tokens:tt)+ ] => {
        closure_to_fn_spec(|s: ReconcileLocalState| {
            let vds = VDeploymentReconcileState::unmarshal(s).unwrap();
            at_step_internal_or!(vds, $($tokens)+)
        })
    };
}

// usage: lift_local(controller_id, vd, at_step_or![step_or_pred+])
pub open spec fn lift_local(controller_id: int, vd: VDeploymentView, step_pred: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), step_pred)
}

// hacky workaround for type conversion bug: error[E0605]: non-primitive cast: `{integer}` as `builtin::nat`
#[macro_export]
macro_rules! nat0 {
    () => {
        spec_literal_nat("0")
    };
}

#[macro_export]
macro_rules! nat1 {
    () => {
        spec_literal_nat("1")
    };
}

pub use nat0;
pub use nat1;
pub use at_step_internal_or;
pub use at_step_or;
}