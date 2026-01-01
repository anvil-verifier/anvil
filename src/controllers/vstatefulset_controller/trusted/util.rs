use crate::kubernetes_api_objects::spec::resource::*;
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::ReconcileLocalState};
use crate::vstatefulset_controller::trusted::{spec_types::*, step::*};
use crate::vstatefulset_controller::model::reconciler::VStatefulSetReconcileState;
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// usage: at_step![step_or_pred]
// step_or_pred = step | (step, pred)
#[macro_export]
macro_rules! at_step {
    [ $($tokens:tt)? ] => {
        closure_to_fn_spec(|s: ReconcileLocalState| {
            let vsts_state = VStatefulSetReconcileState::unmarshal(s).unwrap();
            at_step_or_internal!(vsts_state, $($tokens)?)
        })
    };
}

// usage: at_step_or![step_or_pred,*]
// step_or_pred = step | (step, pred)
#[macro_export]
macro_rules! at_step_or {
    [ $($tokens:tt)+ ] => {
        closure_to_fn_spec(|s: ReconcileLocalState| {
            let vsts_state = VStatefulSetReconcileState::unmarshal(s).unwrap();
            at_step_or_internal!(vsts_state, $($tokens)+)
        })
    };
}

#[macro_export]
macro_rules! at_step_or_internal {
    ($vsts_state:expr, ($step:expr, $pred:expr)) => {
        $vsts_state.reconcile_step.eq_step($step) && $pred($vsts_state)
    };

    ($vsts_state:expr, $step:expr) => {
        $vsts_state.reconcile_step.eq_step($step)
    };

    ($vsts_state:expr, $head:tt, $($tail:tt)+) => {
        at_step_or_internal!($vsts_state, $head) || at_step_or_internal!($vsts_state, $($tail)+)
    };
}

// usage: lift_local(controller_id, vsts, at_step_or![step_or_pred+])
pub open spec fn lift_local(controller_id: int, vsts: VStatefulSetView, step_pred: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    Cluster::at_expected_reconcile_states(controller_id, vsts.object_ref(), step_pred)
}

pub use at_step_or_internal;
pub use at_step_or;
pub use at_step;

}
