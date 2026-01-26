use crate::kubernetes_api_objects::spec::{resource::*, prelude::*};
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::*, esr::*, message::*};
use crate::vstatefulset_controller::trusted::{spec_types::*, step::*, step::VStatefulSetReconcileStepView::*, rely::*};
use crate::vstatefulset_controller::model::{reconciler::*, install::*};
use crate::vstatefulset_controller::proof::{helper_invariants, guarantee};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// just to make Verus happy
pub uninterp spec fn dummy<T>(t: T) -> bool;

// allow status and rv updates
pub open spec fn weakly_eq(obj: DynamicObjectView, obj_prime: DynamicObjectView) -> bool {
    &&& obj.metadata.without_resource_version() == obj_prime.metadata.without_resource_version()
    &&& obj.kind == obj_prime.kind
    &&& obj.spec == obj_prime.spec
}

pub open spec fn has_vsts_prefix(name: StringView) -> bool {
    exists |suffix| name == VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + suffix
}

// Other controllers don't create PVC matching VSTS's PVC template.
// this is stronger than storage_matches that we check pvc_template_name
// instead of pvc_template_name + existing a pod whose pvc matches requested obj
// Because even if there is no such pod running in cluster,
// PVC matching VSTS's template shouldn't be touched
pub open spec fn pvc_name_match(name: StringView, vsts_name: StringView) -> bool {
    exists |i: (StringView, nat)| name == #[trigger] pvc_name(i.0, vsts_name, i.1)
        && dash_free(i.0) // PVC template name should not contain dash
}

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

// usage: and!(pred1, pred2, ...)
#[macro_export]
macro_rules! and {
    ($($tokens:tt)+) => {
        closure_to_fn_spec(|s| {
            and_internal!(s, $($tokens)+)
        })
    };
}

#[macro_export]
macro_rules! and_internal {
    ($s:expr, $head:expr) => {
        $head($s)
    };

    ($s:expr, $head:expr, $($tail:tt)+) => {
        and_internal!($s, $head) && and_internal!($s, $($tail)+)
    };
}

// usage: or!(pred1, pred2, ...)
#[macro_export]
macro_rules! or {
    ($($tokens:tt)+) => {
        closure_to_fn_spec(|s| {
            or_internal!(s, $($tokens)+)
        })
    };
}

#[macro_export]
macro_rules! or_internal {
    ($s:expr, $head:expr) => {
        $head($s)
    };

    ($s:expr, $head:expr, $($tail:tt)+) => {
        or_internal!($s, $head) || or_internal!($s, $($tail)+)
    };
}

#[macro_export]
macro_rules! not {
    ( $pred:expr ) => {
        closure_to_fn_spec(|s| {
            ! $pred(s)
        })
    };
}

pub use or;
pub use or_internal;
pub use and;
pub use and_internal;
pub use not;

pub open spec fn lifted_vsts_rely_condition(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    lift_state(|s| {
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] vsts_rely(other_id, cluster.installed_types)(s)
    })
}

}