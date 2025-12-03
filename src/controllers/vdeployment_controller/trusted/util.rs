use crate::kubernetes_api_objects::spec::{
    prelude::*, pod_template_spec::PodTemplateSpecView, label_selector::LabelSelectorView
};
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::ReconcileLocalState};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::trusted::{spec_types::*, liveness_theorem::*};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// some util spec functions are moved here from model::reconciler
// so we can share them with high-level specs and proofs for VD
pub open spec fn objects_to_vrs_list(objs: Seq<DynamicObjectView>) -> (vrs_list: Option<Seq<VReplicaSetView>>) {
    if objs.filter(|o: DynamicObjectView| VReplicaSetView::unmarshal(o).is_err()).len() != 0 {
        None
    } else {
        Some(objs.map_values(|o: DynamicObjectView| VReplicaSetView::unmarshal(o).unwrap()))
    }
}

pub open spec fn valid_owned_vrs(vrs: VReplicaSetView, vd: VDeploymentView) -> bool {
    // weaker version of well_formed, only need the key to be in etcd
    // and corresponding objects can pass the filter
    &&& vrs.metadata.name is Some
    &&& vrs.metadata.namespace is Some
    &&& vrs.metadata.namespace->0 == vd.metadata.namespace->0
    &&& vrs.state_validation()
    // shall not be deleted and is owned by vd
    &&& vrs.metadata.deletion_timestamp is None
    &&& vrs.metadata.owner_references_contains(vd.controller_owner_ref())
}

pub open spec fn filter_old_and_new_vrs(vd: VDeploymentView, vrs_list: Seq<VReplicaSetView>) -> (res: (Option<VReplicaSetView>, Seq<VReplicaSetView>))
{
    // first vrs that match template and has non-zero replicas
    // non-zero replicas ensures the stability of esr
    let reusable_vrs_list = vrs_list.filter(match_template_without_hash(vd.spec.template));
    // TODO: can be replaced with sort based on abs(replicas-vd.spec.replicas)
    let nonempty_vrs_filter = |vrs: VReplicaSetView| vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0;
    let reusable_vrs = if reusable_vrs_list.len() > 0 {
        if reusable_vrs_list.filter(nonempty_vrs_filter).len() > 0 {
            Some(reusable_vrs_list.filter(nonempty_vrs_filter).first())
        } else {
            Some(reusable_vrs_list.first())
        }
    } else {
        None
    };
    let old_vrs_list = vrs_list.filter(|vrs: VReplicaSetView| {
        &&& reusable_vrs is None || vrs.metadata.uid != reusable_vrs->0.metadata.uid
        &&& vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0
    });
    (reusable_vrs, old_vrs_list)
}

// there is no way to ensure vd does not have label with key "pod-template-hash",
// so here we remote key from both sides
pub open spec fn match_template_without_hash(template: PodTemplateSpecView) -> spec_fn(VReplicaSetView) -> bool {
    |vrs: VReplicaSetView| {
        PodTemplateSpecView {
            metadata: Some(ObjectMetaView {
                labels: Some(template.metadata->0.labels->0.remove("pod-template-hash"@)),
                ..template.metadata->0
            }),
            ..template
        } == PodTemplateSpecView {
            metadata: Some(ObjectMetaView {
                labels: Some(vrs.spec.template->0.metadata->0.labels->0.remove("pod-template-hash"@)),
                ..vrs.spec.template->0.metadata->0
            }),
            ..vrs.spec.template->0
        }
    }
}

pub open spec fn match_replicas(vd: VDeploymentView, vrs: VReplicaSetView) -> bool {
    vd.spec.replicas.unwrap_or(1) == vrs.spec.replicas.unwrap_or(1 as int)
}

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

// usage: at_step![step_or_pred]
// step_or_pred = step | (step, pred)
#[macro_export]
macro_rules! at_step {
    [ $($tokens:tt)? ] => {
        closure_to_fn_spec(|s: ReconcileLocalState| {
            let vds = VDeploymentReconcileState::unmarshal(s).unwrap();
            at_step_or_internal!(vds, $($tokens)?)
        })
    };
}

// usage: at_step_or![step_or_pred,*]
// step_or_pred = step | (step, pred)
#[macro_export]
macro_rules! at_step_or {
    [ $($tokens:tt)+ ] => {
        closure_to_fn_spec(|s: ReconcileLocalState| {
            let vds = VDeploymentReconcileState::unmarshal(s).unwrap();
            at_step_or_internal!(vds, $($tokens)+)
        })
    };
}

#[macro_export]
macro_rules! at_step_or_internal {
    ($vds:expr, ($step:expr, $pred:expr)) => {
        $vds.reconcile_step.eq_step($step) && $pred($vds)
    };

    // eq_step is the tricky workaround for error, see src/controllers/vdeployment_controller/trusted/step.rs
    ($vds:expr, $step:expr) => {
        $vds.reconcile_step.eq_step($step)
    };

    ($vds:expr, $head:tt, $($tail:tt)+) => {
        at_step_or_internal!($vds, $head) || at_step_or_internal!($vds, $($tail)+)
    };
}

// usage: lift_local(controller_id, vd, at_step_or![step_or_pred+])
pub open spec fn lift_local(controller_id: int, vd: VDeploymentView, step_pred: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), step_pred)
}

pub use at_step_or_internal;
pub use at_step_or;
pub use at_step;
pub use or;
pub use or_internal;
pub use and;
pub use and_internal;

pub proof fn and_eq(p: StatePred<ClusterState>, q: StatePred<ClusterState>)
    ensures lift_state(and!(p, q)) == lift_state(p).and(lift_state(q)),
{
    temp_pred_equality(lift_state(and!(p, q)), lift_state(p).and(lift_state(q)))
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

#[macro_export]
macro_rules! int0 {
    () => {
        spec_literal_int("0")
    };
}

#[macro_export]
macro_rules! int1 {
    () => {
        spec_literal_int("1")
    };
}

pub use nat0;
pub use nat1;
pub use int0;
pub use int1;

}