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

pub open spec fn vsts_cluster_invariants(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
) -> bool {
    &&& spec.entails(always(lift_action(cluster.next())))
    &&& spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1))))
    &&& spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i)))
    &&& spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i)))
    &&& spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i))))
    &&& spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i))))
    &&& spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))))
    &&& spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id))))
    &&& spec.entails(always(lift_state(Cluster::crash_disabled(controller_id))))
    &&& spec.entails(always(lift_state(Cluster::req_drop_disabled())))
    &&& spec.entails(always(lift_state(Cluster::pod_monkey_disabled())))
    &&& spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id())))
    &&& spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())))
    &&& spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))))
    &&& spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())))
    &&& spec.entails(always(lift_state(Cluster::etcd_objects_have_unique_uids())))
    &&& spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())))
    &&& spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>())))
    &&& spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id))))
    &&& spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())))
    &&& spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())))
    &&& spec.entails(always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(controller_id))))
    &&& spec.entails(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))))
    &&& spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))))
    &&& spec.entails(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))))
    &&& spec.entails(always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id))))
    &&& spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VStatefulSetView>(controller_id))))
    &&& spec.entails(always(lift_state(Cluster::etcd_is_finite())))
    &&& spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref()))))
    &&& spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id))))
    &&& spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers())))
    &&& spec.entails(always(lift_state(Cluster::desired_state_is(vsts))))
    &&& spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vsts.object_ref()))))
    &&& spec.entails(always(lift_state(helper_invariants::all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_labels(vsts))))
    &&& spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id))))
    &&& spec.entails(always(lift_state(guarantee::every_msg_from_vsts_controller_carries_vsts_key(controller_id))))
    &&& spec.entails(always(lift_state(vsts_rely_conditions(cluster, controller_id))))
    &&& spec.entails(always(lift_state(garbage_collector_does_not_delete_vsts_pod_objects(vsts))))
    // no sent request at certain steps
    &&& spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![Init]))))
    &&& spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC]))))
    &&& spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC]))))
    &&& spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC]))))
    &&& spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreateNeeded]))))
    &&& spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![UpdateNeeded]))))
    &&& spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned]))))
    &&& spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated]))))
    // there is always sent request/pending response at certain steps for vsts to transit to next state
    &&& spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterListPod]))))
    &&& spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC]))))
    &&& spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC]))))
    &&& spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded]))))
    &&& spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded]))))
    &&& spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned]))))
    &&& spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated]))))
}

pub use or;
pub use or_internal;
pub use and;
pub use and_internal;
pub use not;

}