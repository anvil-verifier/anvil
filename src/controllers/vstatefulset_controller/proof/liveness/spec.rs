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
    proof::{predicate::*, liveness::*},
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
        Cluster::desired_state_is(vsts)
    )
}

}
