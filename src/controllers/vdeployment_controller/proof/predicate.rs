use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*
};
use crate::vdeployment_controller::{
    trusted::{step::*, spec_types::*, rely_guarantee::vd_rely},
    model::{install::*, reconciler::*},
};
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

pub open spec fn pending_list_req_in_flight(vd: VDeploymentView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0();
        let req = msg.content.get_APIRequest_0();
        &&& msg.src.is_controller_id(controller_id)
        &&& msg.dst == HostId::APIServer
        &&& req.is_ListRequest()
        &&& req.get_ListRequest_0().kind == VDeploymentView::kind()
        &&& req.get_ListRequest_0().namespace == vd.metadata.namespace.unwrap()
    }
}

pub open spec fn exists_list_resp_in_flight(vd: VDeploymentView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& pending_list_req_in_flight(vd, controller_id)(s)
        let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0();
        &&& exists |resp: Message| {
            &&& s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_list_response().res.is_Ok()
            &&& {
                let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                &&& objects_to_vrs_list(resp_objs).is_Some()
                &&& resp_objs.no_duplicates()
                &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] obj.metadata.namespace == vd.metadata.namespace
            }
        }
    }
}

pub open spec fn vd_rely_condition(cluster: Cluster, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
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
            let req = msg.content.get_delete_request(); 
            &&& msg.content.is_delete_request()
            &&& req.preconditions.is_Some()
            &&& req.preconditions.unwrap().uid.is_Some()
            &&& req.preconditions.unwrap().uid.unwrap() < s.api_server.uid_counter
            &&& s.resources().contains_key(req.key) ==> {
                let etcd_obj = s.resources()[req.key];
                let owner_references = etcd_obj.metadata.owner_references.get_Some_0();
                ||| (!etcd_obj.metadata.owner_references.is_Some() && owner_references.contains(vd.controller_owner_ref()))
                ||| etcd_obj.metadata.uid.unwrap() > req.preconditions.unwrap().uid.unwrap()
            }
        }
    }
}

pub open spec fn next_with_wf(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    always(lift_action(cluster.next()))
    .and(tla_forall(|input| cluster.api_server_next().weak_fairness(input)))
    .and(tla_forall(|input| cluster.builtin_controllers_next().weak_fairness(input)))
    .and(tla_forall(|input: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, input.0, input.1))))
    .and(tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness((controller_id, input))))
    .and(tla_forall(|input| cluster.disable_crash().weak_fairness(input)))
    .and(tla_forall(|input| cluster.external_next().weak_fairness((controller_id, input))))
    .and(cluster.disable_req_drop().weak_fairness(()))
    .and(cluster.disable_pod_monkey().weak_fairness(()))
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
        vd_rely_condition(cluster, controller_id),
        garbage_collector_does_not_delete_vd_pods(vd)
    )
}

// just to make Verus happy
pub uninterp spec fn dummy_trigger_n(n: nat) -> bool;
pub uninterp spec fn dummy_trigger_ex(ex: Execution<ClusterState>) -> bool;
pub uninterp spec fn dummy_trigger_transition(input: DynamicObjectView, resp_o: Option<ResponseContent>, s: ReconcileLocalState) -> bool;

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

// usage: at_step![step,*]
// step_or_pred = step | (step, pred)
#[macro_export]
macro_rules! at_step_or {
    ($($tokens:tt)+) => {
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

// usage: lift_local(controller_id, vd, at_step_or!(step_or_pred+])
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
pub use at_step_or_internal;
pub use at_step_or;
pub use and;
pub use and_internal;
}