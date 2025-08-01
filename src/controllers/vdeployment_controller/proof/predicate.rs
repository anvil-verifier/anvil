use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::vdeployment_controller::{
    trusted::{rely_guarantee::*, step::*, spec_types::*},
    model::{install::*, reconciler::*},
    proof::helper_invariants,
};
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*
};
use crate::vdeployment_controller::{
    trusted::{step::*, spec_types::*, util::*,
        rely_guarantee::vd_rely, liveness_theorem::*},
    model::{install::*, reconciler::*},
};
use crate::vreplicaset_controller::trusted::spec_types::VReplicaSetView;
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use vstd::prelude::*;

verus! {

// predicates used for liveness reasoning
pub open spec fn at_vd_step_with_vd(vd: VDeploymentView, controller_id: int, step_pred: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
        let local_state = s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state;
        &&& s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
        &&& VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).is_ok()
        &&& VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).is_ok()
        &&& triggering_cr.object_ref() == vd.object_ref()
        &&& triggering_cr.spec() == vd.spec()
        &&& triggering_cr.metadata().uid == vd.metadata().uid
        &&& step_pred(local_state)
    }
}

pub open spec fn no_pending_req_in_cluster(vd: VDeploymentView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        Cluster::no_pending_req_msg(controller_id, s, vd.object_ref())
    }
}

pub open spec fn req_msg_is_list_vrs_req(vd: VDeploymentView, controller_id: int, req_msg: Message) -> bool {
    let request = req_msg.content.get_APIRequest_0();
    &&& req_msg.src == HostId::Controller(controller_id, vd.object_ref())
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content.is_APIRequest()
    &&& request.is_ListRequest()
    &&& request.get_ListRequest_0() == ListRequest {
        kind: VReplicaSetView::kind(),
        namespace: vd.metadata.namespace.unwrap(),
    }
}

pub open spec fn pending_list_req_in_flight(vd: VDeploymentView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_list_vrs_req(vd, controller_id, req_msg)
    }
}

pub open spec fn req_msg_is_pending_list_req_in_flight(vd: VDeploymentView, controller_id: int, req_msg: Message,) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_list_vrs_req(vd, controller_id, req_msg)
    }
}

// should be used with VReplicaSetView::marshal_preserves_integrity()
// resp is list resp matching req && resp content match etcd
pub open spec fn exists_pending_list_resp_in_flight_and_match_req(vd: VDeploymentView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        // predicate on req_msg, it's not in_flight
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_list_vrs_req(vd, controller_id, req_msg)
        // predicate on resp_msg
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg_is_ok_list_resp_containing_matched_vrs(s, vd, resp_msg)
        }
    }
}

pub open spec fn resp_msg_is_pending_list_resp_in_flight_and_match_req(
    vd: VDeploymentView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        // predicate on req_msg, it's not in_flight
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_list_vrs_req(vd, controller_id, req_msg)
        // predicate on resp_msg
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg_is_ok_list_resp_containing_matched_vrs(s, vd, resp_msg)
    }
}

pub open spec fn resp_msg_is_ok_list_resp_containing_matched_vrs(
    s: ClusterState, vd: VDeploymentView, resp_msg: Message
) -> bool {
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    let vrs_list = objects_to_vrs_list(resp_objs).unwrap();
    &&& resp_msg.content.is_list_response()
    &&& resp_msg.content.get_list_response().res is Ok
    &&& objects_to_vrs_list(resp_objs) is Some
    &&& resp_objs.no_duplicates()
    &&& resp_objs == s.resources().values().filter(list_vrs_obj_filter(vd)).to_seq()
    &&& filter_old_and_new_vrs(vd, vrs_list.filter(|vrs| valid_owned_object(vrs, vd))) == filter_old_and_new_vrs_on_etcd(vd, s.resources())
    // these can be inferred from list_vrs_obj_filter and cr_in_etcd_is_well_formed
    // just to make proof easier
    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] VReplicaSetView::unmarshal(obj) is Ok
    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] valid_owned_object(VReplicaSetView::unmarshal(obj).unwrap(), vd)
}

pub open spec fn req_msg_is_create_vrs_req(
    vd: VDeploymentView, controller_id: int, req_msg: Message
) -> bool {
    let request = req_msg.content.get_APIRequest_0().get_CreateRequest_0();
    &&& req_msg.src == HostId::Controller(controller_id, vd.object_ref())
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content.is_APIRequest()
    &&& req_msg.content.get_APIRequest_0().is_CreateRequest()
    &&& request == CreateRequest {
        namespace: vd.metadata.namespace.unwrap(),
        obj: make_replica_set(vd).marshal()
    }
}

pub open spec fn pending_create_new_vrs_req_in_flight(
    vd: VDeploymentView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_create_vrs_req(vd, controller_id, req_msg)
    }
}

pub open spec fn req_msg_is_pending_create_new_vrs_req_in_flight(
    vd: VDeploymentView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_create_vrs_req(vd, controller_id, req_msg)
    }
}

pub open spec fn resp_msg_is_ok_create_new_vrs_resp(
    vd: VDeploymentView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_create_vrs_req(vd, controller_id, req_msg)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg.content.is_create_response()
        &&& resp_msg.content.get_create_response().res is Ok
    }
}

pub open spec fn exists_resp_msg_is_ok_create_new_vrs_resp(
    vd: VDeploymentView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_create_vrs_req(vd, controller_id, req_msg)
        &&& exists |resp_msg| {
            // predicate on resp_msg
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            // we don't need info on content of the response at the moment
            &&& resp_msg.content.is_create_response()
            &&& resp_msg.content.get_create_response().res is Ok
        }
    }
}

// TODO: it's possible to eliminate resp_msg here as it can be crafted from req
pub open spec fn resp_msg_is_ok_get_then_update_resp_with_replicas(
    vd: VDeploymentView, controller_id: int, resp_msg: Message, n: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_get_then_update_req_with_replicas(vd, controller_id, req_msg, n)(s)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg.content.is_get_then_update_response()
        &&& resp_msg.content.get_get_then_update_response().res is Ok
    }
}

pub open spec fn exists_resp_msg_is_ok_get_then_update_resp_with_replicas(
    vd: VDeploymentView, controller_id: int, n: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& req_msg_is_get_then_update_req_with_replicas(vd, controller_id, req_msg, n)(s)
        &&& exists |resp_msg| {
            // predicate on resp_msg
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            // we don't need info on content of the response at the moment
            &&& resp_msg.content.is_get_then_update_response()
            &&& resp_msg.content.get_get_then_update_response().res is Ok
        }
    }
}

pub open spec fn req_msg_is_get_then_update_req_with_replicas(
    vd: VDeploymentView, controller_id: int, req_msg: Message, n: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let request = req_msg.content.get_APIRequest_0().get_GetThenUpdateRequest_0();
        // Q: state.old_vrs_list does not contain the deleted vrs
        let key = request.key();
        let req_vrs = VReplicaSetView::unmarshal(request.obj).unwrap();
        let state = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        &&& req_msg.src == HostId::Controller(controller_id, vd.object_ref())
        &&& req_msg.dst == HostId::APIServer
        &&& req_msg.content.is_APIRequest()
        &&& req_msg.content.get_APIRequest_0().is_GetThenUpdateRequest()
        &&& request.namespace == vd.metadata.namespace.unwrap()
        &&& request.owner_ref == vd.controller_owner_ref()
        &&& VReplicaSetView::unmarshal(request.obj).is_ok()
        &&& s.resources().contains_key(key)
        // step-specific update content
        &&& req_vrs.metadata.owner_references_contains(vd.controller_owner_ref())
        &&& req_vrs.spec.replicas.unwrap_or(1) == n
    }
}

pub open spec fn req_msg_is_pending_get_then_update_req_in_flight_with_replicas(
    vd: VDeploymentView, controller_id: int, req_msg: Message, n: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_get_then_update_req_with_replicas(vd, controller_id, req_msg, n)(s)
    }
}

pub open spec fn pending_get_then_update_req_in_flight_with_replicas(
    vd: VDeploymentView, controller_id: int, n: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_get_then_update_req_with_replicas(vd, controller_id, req_msg, n)(s)
    }
}

// a weaker version of coherence between local cache and etcd
// - only need the key to be in etcd and corresponding objects can pass the filter
// - so current_state_matches can be reached by sending get-then-update request
// this predicate holds since AfterListVRS state
pub open spec fn local_state_is_consistent_with_etcd(vd: VDeploymentView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let vds = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        &&& forall |i| 0 <= i < vds.old_vrs_index ==> {
            // the get-then-update request can succeed
            &&& #[trigger] valid_owned_object(vds.old_vrs_list[i], vd)
            // obj in etcd exists and is owned by vd
            &&& s.resources().contains_key(vds.old_vrs_list[i].object_ref())
            &&& ({
                let etcd_obj = s.resources()[vds.old_vrs_list[i].object_ref()];
                let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj).unwrap();
                // can pass list_vrs_obj_filter
                &&& etcd_obj.kind == VReplicaSetView::kind()
                &&& etcd_obj.metadata.namespace == vd.metadata.namespace
                // can pass objects_to_vrs_list
                &&& VReplicaSetView::unmarshal(etcd_obj).is_ok()
                // can pass filter_old_and_new_vrs_on_etcd
                &&& filter_old_and_new_vrs_on_etcd(vd, s.resources()).1.contains(etcd_vrs)
            })
        }
        &&& vds.old_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref()).no_duplicates()
        // new vrs
        &&& vds.new_vrs is None ==> filter_old_and_new_vrs_on_etcd(vd, s.resources()).0 is None
        &&& vds.new_vrs is Some ==> {
            let new_vrs = vds.new_vrs->0;
            // the get-then-update request can succeed
            &&& valid_owned_object(new_vrs, vd)
            // if it's just created, etcd will not have it yet
            // otherwise obj in etcd exists and is owned by vd
            &&& !pending_create_new_vrs_req_in_flight(vd, controller_id)(s) ==>
                s.resources().contains_key(new_vrs.object_ref())
                && ({
                    let etcd_vrs = VReplicaSetView::unmarshal(s.resources()[new_vrs.object_ref()]).unwrap();
                    // the corresponding object in etcd is a new vrs
                    &&& filter_old_and_new_vrs_on_etcd(vd, s.resources()).0 == Some(etcd_vrs)
                })
        }
    }
}

// new_vrs_replicas is Some(x) -> new vrs exists and has replicas = x; else new vrs does not exist
pub open spec fn etcd_state_is(vd: VDeploymentView, controller_id: int, new_vrs_replicas: Option<int>, old_vrs_list_len: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let objs = s.resources().values().filter(list_vrs_obj_filter(vd)).to_seq();
        let (new_vrs, old_vrs_list) = filter_old_and_new_vrs_on_etcd(vd, s.resources());
        &&& objects_to_vrs_list(objs) is Some
        &&& old_vrs_list.len() == old_vrs_list_len
        &&& match new_vrs_replicas {
            Some(n) => {
                &&& new_vrs is Some
                &&& new_vrs->0.spec.replicas.unwrap_or(1) == n
                &&& match_template_without_hash(vd, new_vrs->0)
            },
            None => {
                new_vrs is None
            }
        }
    }
}

pub open spec fn local_state_is(new_vrs_replicas: Option<int>, old_vrs_list_len: nat) -> spec_fn(VDeploymentReconcileState) -> bool {
    |vds: VDeploymentReconcileState| {
        &&& match new_vrs_replicas {
            Some(n) => {
                &&& vds.new_vrs is Some
                &&& vds.new_vrs->0.spec.replicas.unwrap_or(1) == n
            }
            None => vds.new_vrs is None
        }
        &&& vds.old_vrs_index == old_vrs_list_len
    }
}

pub open spec fn old_vrs_list_len(n: nat) -> spec_fn(VDeploymentReconcileState) -> bool {
    |vds: VDeploymentReconcileState| vds.old_vrs_index == n
}

pub open spec fn vd_rely_condition(vd: VDeploymentView, cluster: Cluster, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| forall |other_id| other_id != controller_id && cluster.controller_models.contains_key(other_id)
                                        ==> #[trigger] vd_rely(other_id)(s)
}

// same as vrs, similar to rely condition. Yet we talk about owner_ref here
pub open spec fn garbage_collector_does_not_delete_vd_pods(vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src.is_BuiltinController()
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        } ==> {
            let req_msg = msg.content.get_delete_request(); 
            &&& msg.content.is_delete_request()
            &&& req_msg.preconditions is Some
            &&& req_msg.preconditions.unwrap().uid is Some
            &&& req_msg.preconditions.unwrap().uid.unwrap() < s.api_server.uid_counter
            &&& s.resources().contains_key(req_msg.key) ==> {
                let etcd_obj = s.resources()[req_msg.key];
                let owner_references = etcd_obj.metadata.owner_references->0;
                ||| (!(etcd_obj.metadata.owner_references is Some) && owner_references.contains(vd.controller_owner_ref()))
                ||| etcd_obj.metadata.uid.unwrap() > req_msg.preconditions.unwrap().uid.unwrap()
            }
        }
    }
}

pub open spec fn cluster_invariants_since_reconciliation(cluster: Cluster, vd: VDeploymentView, controller_id: int) -> StatePred<ClusterState> {
    and!(
        Cluster::crash_disabled(controller_id),
        Cluster::req_drop_disabled(),
        Cluster::pod_monkey_disabled(),
        Cluster::every_in_flight_msg_has_unique_id(),
        Cluster::every_in_flight_msg_has_lower_id_than_allocator(),
        Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id),
        Cluster::each_object_in_etcd_is_weakly_well_formed(),
        cluster.each_builtin_object_in_etcd_is_well_formed(),
        cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>(),
        Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id(),
        Cluster::each_object_in_etcd_has_at_most_one_controller_owner(),
        Cluster::cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(controller_id),
        Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id),
        Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id),
        Cluster::ongoing_reconciles_is_finite(controller_id),
        Cluster::cr_objects_in_reconcile_have_correct_kind::<VDeploymentView>(controller_id),
        Cluster::etcd_is_finite(),
        Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref()),
        Cluster::there_is_the_controller_state(controller_id),
        Cluster::there_is_no_request_msg_to_external_from_controller(controller_id),
        Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id),
        Cluster::desired_state_is(vd),
        vd_rely_condition(vd, cluster, controller_id),
        garbage_collector_does_not_delete_vd_pods(vd)
    )
}

// just to make Verus happy
pub uninterp spec fn dummy<T>(t: T) -> bool;

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
pub use at_step_or_internal;
pub use at_step_or;
pub use at_step;
pub use or;
pub use or_internal;
pub use and;
pub use and_internal;

// General helper predicates
pub open spec fn lifted_vd_rely_condition(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    lift_state(|s| {
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] vd_rely(other_id)(s)
    })
}

pub open spec fn lifted_vd_rely_condition_action(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    lift_action(|s, s_prime| {
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] vd_rely(other_id)(s))
        && (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vd_rely(other_id)(s_prime))
    })
}

pub open spec fn lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id: int) -> TempPred<ClusterState> {
    lift_action(|s, s_prime| {
        (forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s))
        && (forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s_prime))
    })
}

pub open spec fn owner_references_contains_ignoring_uid(meta: ObjectMetaView, orig_or: OwnerReferenceView) -> bool {
    exists |or: OwnerReferenceView| {
        &&& #[trigger] meta.owner_references_contains(or)
        &&& or.block_owner_deletion == orig_or.block_owner_deletion
        &&& or.controller == orig_or.controller
        &&& or.kind == orig_or.kind
        &&& or.name == orig_or.name
    }
}

}