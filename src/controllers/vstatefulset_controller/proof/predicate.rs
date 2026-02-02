// shared predicates and macros

use crate::kubernetes_api_objects::spec::{resource::*, prelude::*};
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::*, esr::*, message::*};
use crate::vstatefulset_controller::trusted::{spec_types::*, step::*, step::VStatefulSetReconcileStepView::*, rely};
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

pub open spec fn pod_weakly_eq(pod: PodView, pod_prime: PodView) -> bool {
    &&& pod.metadata.without_resource_version().without_labels() == pod_prime.metadata.without_resource_version().without_labels()
    &&& pod.spec is Some
    &&& pod_prime.spec is Some
    &&& pod.spec->0.without_volumes().without_hostname().without_subdomain()
        == pod_prime.spec->0.without_volumes().without_hostname().without_subdomain()
}

pub open spec fn has_vsts_prefix(name: StringView) -> bool {
    exists |suffix| name == VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + suffix
}

pub open spec fn valid_owned_object_filter(vsts: VStatefulSetView) -> spec_fn(DynamicObjectView) -> bool {
    |obj: DynamicObjectView| {
        &&& obj.kind == Kind::PodKind
        &&& obj.metadata.name is Some
        &&& obj.metadata.namespace is Some
        &&& obj.metadata.namespace->0 == vsts.metadata.namespace->0
        &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
    }
}

pub open spec fn req_msg_or_none(s: ClusterState, vsts_key: ObjectRef, controller_id: int) -> (req_msg: Option<Message>) {
    s.ongoing_reconciles(controller_id)[vsts_key].pending_req_msg
}

pub open spec fn resp_msg_or_none(s: ClusterState, vsts_key: ObjectRef, controller_id: int) -> (resp_msg: Option<Message>) {
    if req_msg_or_none(s, vsts_key, controller_id) is Some && exists |resp_msg: Message| {
        &&& #[trigger] s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg_or_none(s, vsts_key, controller_id)->0)
    } {
        Some(choose |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg_or_none(s, vsts_key, controller_id)->0)
        })
    } else {
        None
    }
}

pub open spec fn req_msg_is(msg: Message, vsts_key: ObjectRef, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| Cluster::pending_req_msg_is(controller_id, s, vsts_key, msg)
}

pub open spec fn resp_msg_is(msg: Message, vsts_key: ObjectRef, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| resp_msg_or_none(s, vsts_key, controller_id) == Some(msg)
}

pub open spec fn outdated_obj_keys_in_etcd(s: ClusterState, vsts: VStatefulSetView) -> Set<ObjectRef> {
    s.resources().dom().filter(outdated_obj_key_filter(s, vsts))
}

pub open spec fn outdated_obj_key_filter(s: ClusterState, vsts: VStatefulSetView) -> spec_fn(ObjectRef) -> bool {
    |key: ObjectRef| {
        &&& exists |ord: nat| ord < replicas(vsts) && key == ObjectRef {
            kind: PodView::kind(),
            name: #[trigger] pod_name(vsts.metadata.name->0, ord),
            namespace: vsts.metadata.namespace->0
        }
        &&& PodView::unmarshal(s.resources()[key]) is Ok
        &&& !pod_spec_matches(vsts, PodView::unmarshal(s.resources()[key])->Ok_0)
    }
}

pub open spec fn pvc_cnt(vsts: VStatefulSetView) -> nat {
    match vsts.spec.volume_claim_templates {
        Some(pvc_templates) => pvc_templates.len(),
        None => 0,
    }
}

pub open spec fn replicas(vsts: VStatefulSetView) -> nat {
    match vsts.spec.replicas {
        Some(r) => r as nat,
        None => 1,
    }
}

pub open spec fn cluster_invariants_since_reconciliation(cluster: Cluster, vsts: VStatefulSetView, controller_id: int) -> StatePred<ClusterState> {
    and!(
        Cluster::crash_disabled(controller_id),
        Cluster::req_drop_disabled(),
        Cluster::pod_monkey_disabled(),
        Cluster::every_in_flight_msg_has_unique_id(),
        Cluster::every_in_flight_msg_has_lower_id_than_allocator(),
        Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id),
        Cluster::each_object_in_etcd_is_weakly_well_formed(),
        Cluster::etcd_objects_have_unique_uids(),
        cluster.each_builtin_object_in_etcd_is_well_formed(),
        cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>(),
        Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id(),
        Cluster::each_object_in_etcd_has_at_most_one_controller_owner(),
        Cluster::cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(controller_id),
        Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, vsts),
        Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id),
        Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id),
        Cluster::ongoing_reconciles_is_finite(controller_id),
        Cluster::cr_objects_in_reconcile_have_correct_kind::<VStatefulSetView>(controller_id),
        Cluster::etcd_is_finite(),
        Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref()),
        Cluster::there_is_the_controller_state(controller_id),
        Cluster::there_is_no_request_msg_to_external_from_controller(controller_id),
        Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id),
        Cluster::no_pending_request_to_api_server_from_non_controllers(),
        Cluster::desired_state_is(vsts),
        Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vsts.object_ref()),
        helper_invariants::all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_labels(vsts),
        helper_invariants::all_pvcs_in_etcd_matching_vsts_have_no_owner_ref(vsts),
        helper_invariants::vsts_in_reconciles_has_no_deletion_timestamp(vsts, controller_id),
        guarantee::vsts_internal_guarantee_conditions(controller_id),
        guarantee::every_msg_from_vsts_controller_carries_vsts_key(controller_id),
        rely::vsts_rely_conditions(cluster, controller_id),
        rely::garbage_collector_does_not_delete_vsts_pod_objects(vsts)
    )
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

// Helper spec to check if a pod name matches a vsts naming pattern
pub open spec fn pod_name_match(compared_pod_name: StringView, parent_name: StringView) -> bool {
    exists |ord: nat| compared_pod_name == pod_name(parent_name, ord)
}

// usage: at_step![step_or_pred]
// step_or_pred = step | (step, pred)
#[macro_export]
macro_rules! at_step {
    [ $($tokens:tt)? ] => {
        closure_to_fn_spec(|s: ReconcileLocalState| {
            let vsts_state = VStatefulSetReconcileState::unmarshal(s).unwrap();
            locally_at_step_or!(vsts_state, $($tokens)?)
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
            locally_at_step_or!(vsts_state, $($tokens)+)
        })
    };
}

#[macro_export]
macro_rules! locally_at_step_or {
    ($vsts_state:expr, ($step:expr, $pred:expr)) => {
        $vsts_state.reconcile_step.eq_step($step) && $pred($vsts_state)
    };

    ($vsts_state:expr, $step:expr) => {
        $vsts_state.reconcile_step.eq_step($step)
    };

    ($vsts_state:expr, $head:tt, $($tail:tt)+) => {
        locally_at_step_or!($vsts_state, $head) || locally_at_step_or!($vsts_state, $($tail)+)
    };
}

// usage: lift_local(controller_id, vsts, at_step_or![step_or_pred+])
pub open spec fn lift_local(controller_id: int, vsts: VStatefulSetView, step_pred: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    Cluster::at_expected_reconcile_states(controller_id, vsts.object_ref(), step_pred)
}

pub use locally_at_step_or;
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