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

pub open spec fn pending_req_in_flight_and(vd: VDeploymentView, controller_id: int, req_pred: spec_fn(VDeploymentView, APIRequest) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0();
        let req = msg.content.get_APIRequest_0();
        // TODO: do we need this line?
        &&& Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), msg)
        &&& msg.src.is_controller_id(controller_id)
        &&& msg.dst == HostId::APIServer
        &&& req_pred(vd, req)
    }
}

pub open spec fn is_list_req() -> spec_fn(vd: VDeploymentView, req: APIRequest) -> bool {
    |vd: VDeploymentView, req: APIRequest| {
        &&& req.is_ListRequest()
        &&& req.get_ListRequest_0().kind == VDeploymentView::kind()
        &&& req.get_ListRequest_0().namespace == vd.metadata.namespace.unwrap()
    }
}

pub open spec fn vd_rely_condition(cluster: Cluster, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                      ==> #[trigger] vd_rely(other_id)(s)
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

pub open spec fn cluster_invariants(vd: VDeploymentView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())))
    .and(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())))
    .and(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>())))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id))))
    .and(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())))
    .and(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())))
    .and(always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(controller_id))))
    .and(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))))
    .and(always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id))))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VDeploymentView>(controller_id))))
    .and(always(lift_state(Cluster::etcd_is_finite())))
    .and(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())))))
    .and(always(lift_state(Cluster::there_is_the_controller_state(controller_id))))
    .and(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))))
    .and(always(lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id))))
    .and(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![Init])))))
    .and(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterListVRS])))))
    .and(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterCreateNewVRS])))))
    .and(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterScaleNewVRS])))))
    .and(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterScaleDownOldVRS])))))
}

pub open spec fn invariants_since_phase_n(cluster: Cluster, controller_id: int, vd: VDeploymentView, n: nat) -> TempPred<ClusterState>
    decreases n
{
    // match n { 0 => {...}}:
    // expected `nat`, found integer
    if n ==0 {
        cluster_invariants(vd, cluster, controller_id)
        .and(next_with_wf(cluster, controller_id))
        .and(always(lift_state(vd_rely_condition(cluster, controller_id))))
    } else if n == 1 {
        invariants_since_phase_n(cluster, controller_id, vd, 0)
        .and(always(lift_state(Cluster::crash_disabled(controller_id))))
        .and(always(lift_state(Cluster::req_drop_disabled())))
        .and(always(lift_state(Cluster::pod_monkey_disabled())))
        .and(always(lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, vd))))
    } else {
        true_pred()
    }
}

// just to make Verus happy
pub uninterp spec fn dummy_trigger_n(n: nat) -> bool;
pub uninterp spec fn dummy_trigger_ex(ex: Execution<ClusterState>) -> bool;
pub uninterp spec fn dummy_trigger_transition(input: DynamicObjectView, resp_o: Option<ResponseContent>, s: ReconcileLocalState) -> bool;

#[macro_export]
macro_rules! at_step_internal_or {
    ($vds:expr, ($step:expr, $pred:expr)) => {
        $vds.reconcile_step.eq_step($step) && $pred($vds)
    };

    // eq_step is the tricky workaround for error, see src/v2/controllers/vdeployment_controller/trusted/step.rs
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