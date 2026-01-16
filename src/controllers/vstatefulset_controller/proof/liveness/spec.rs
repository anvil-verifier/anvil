#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::{
    spec::{api_server::{state_machine::*, types::*}, cluster::*, controller::types::*, message::*, esr::*,},
    proof::{controller_runtime_liveness::*, network::*},
};

use crate::temporal_logic::{defs::*, rules::*};
use crate::vstatefulset_controller::{
    model::{install::*, reconciler::*},
    trusted::{liveness_theorem::*, rely::*, spec_types::*, step::*, step::VStatefulSetReconcileStepView::*},
    proof::{predicate::*, liveness::*, guarantee, helper_invariants},
};
use crate::reconciler::spec::io::*;
use vstd::{map::*, map_lib::*, math::*, prelude::*};

verus! {

pub open spec fn next_with_wf(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    always(lift_action(cluster.next()))
    .and(tla_forall(|input| cluster.api_server_next().weak_fairness(input)))
    .and(tla_forall(|input| cluster.builtin_controllers_next().weak_fairness(input)))
    .and(tla_forall(|input: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, input.0, input.1))))
    .and(tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness((controller_id, input))))
    .and(tla_forall(|input| cluster.external_next().weak_fairness((controller_id, input))))
    .and(cluster.disable_crash().weak_fairness(controller_id))
    .and(cluster.disable_req_drop().weak_fairness(()))
    .and(cluster.disable_pod_monkey().weak_fairness(()))
}

pub open spec fn vsts_cluster_invariants(
    vsts: VStatefulSetView, cluster: Cluster, controller_id: int
) -> TempPred<ClusterState> {
    always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))
    .and(always(lift_state(Cluster::there_is_the_controller_state(controller_id))))
    .and(always(lift_state(Cluster::crash_disabled(controller_id))))
    .and(always(lift_state(Cluster::req_drop_disabled())))
    .and(always(lift_state(Cluster::pod_monkey_disabled())))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_unique_id())))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())))
    .and(always(lift_state(Cluster::etcd_objects_have_unique_uids())))
    .and(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())))
    .and(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>())))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id))))
    .and(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())))
    .and(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())))
    .and(always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(controller_id))))
    .and(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))))
    .and(always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id))))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VStatefulSetView>(controller_id))))
    .and(always(lift_state(Cluster::etcd_is_finite())))
    .and(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref()))))
    .and(always(lift_state(Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id))))
    .and(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers())))
    .and(always(lift_state(Cluster::desired_state_is(vsts))))
    .and(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vsts.object_ref()))))
    .and(always(lift_state(helper_invariants::all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_labels(vsts))))
    .and(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id))))
    .and(always(lift_state(guarantee::every_msg_from_vsts_controller_carries_vsts_key(controller_id))))
    .and(always(lift_state(vsts_rely_conditions(cluster, controller_id))))
    .and(always(lift_state(garbage_collector_does_not_delete_vsts_pod_objects(vsts))))
    // no sent request at certain steps
    .and(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![Init]))))
    .and(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC]))))
    .and(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC]))))
    .and(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC]))))
    .and(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreateNeeded]))))
    .and(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![UpdateNeeded]))))
    .and(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned]))))
    .and(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated]))))
    // there is always sent request/pending response at certain steps for vsts to transit to next state
    .and(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterListPod]))))
    .and(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC]))))
    .and(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC]))))
    .and(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded]))))
    .and(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded]))))
    .and(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned]))))
    .and(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated]))))
}

}
