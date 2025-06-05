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
#[macro_export]
macro_rules! at_step_internal {
    ($vds:expr, $step:expr) => {
        $vds.reconcile_step == $step
    };

    ($vds:expr, ($step:expr, $pred:expr)) => {
        $vds.reconcile_step == $step && $pred($vds)
    };

    ($vds:expr, $head:tt, $($tail:tt)+) => {
        at_step_internal!($vds, $head) || at_step_internal!($vds, $($tail)+)
    };
}

// usage: at_step!(step,*)
// step* = step | (step, pred)
#[macro_export]
macro_rules! at_step {
    ( $($tokens:tt)+ ) => {
        |s: ReconcileLocalState| {
            let vds = VDeploymentReconcileState::unmarshal(s).unwrap();
            at_step_internal!(vds, $($tokens)+)
        }
    };
}

// usage: cluster_at_step!(step,*)
#[macro_export]
macro_rules! cluster_at_step {
    ($controller_id:expr, $vd:expr, $($tokens:tt)+ ) => {
        Cluster::at_expected_reconcile_states($controller_id, $vd.object_ref(), at_step!($($tokens)+))
    }
}

// usage: temp_at_step!(step,*)
#[macro_export]
macro_rules! temp_at_step {
    ($controller_id:expr, $vd:expr, $($tokens:tt)+ ) => {
        lift_state(cluster_at_step!($controller_id, $vd, $($tokens)+))
    }
}

pub use at_step_internal;
pub use at_step;
pub use cluster_at_step;
pub use temp_at_step;
}