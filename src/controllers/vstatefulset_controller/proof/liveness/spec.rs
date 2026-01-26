#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::{
    proof::{controller_runtime_liveness::*, network::*},
    spec::{
        api_server::{state_machine::*, types::*},
        cluster::*,
        controller::types::*,
        esr::*,
        message::*,
    },
};

use crate::reconciler::spec::io::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstatefulset_controller::{
    model::{install::*, reconciler::*},
    proof::{guarantee, helper_invariants, helper_lemmas::*, liveness::*, predicate::*},
    trusted::{
        liveness_theorem::*, rely::*, spec_types::*, step::VStatefulSetReconcileStepView::*,
        step::*,
    },
};
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

pub proof fn next_with_wf_is_stable(cluster: Cluster, controller_id: int)
    ensures valid(stable(next_with_wf(cluster, controller_id))),
{
    always_p_is_stable(lift_action(cluster.next()));
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.api_server_next());
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.builtin_controllers_next());
    cluster.tla_forall_controller_next_weak_fairness_is_stable(controller_id);
    cluster.tla_forall_schedule_controller_reconcile_weak_fairness_is_stable(controller_id);
    cluster.tla_forall_external_next_weak_fairness_is_stable(controller_id);
    assert(valid(stable(cluster.disable_crash().weak_fairness(controller_id)))) by {
        let split_always = always(lift_state(cluster.disable_crash().pre(controller_id))).implies(eventually(lift_action(cluster.disable_crash().forward(controller_id))));
        always_p_is_stable::<ClusterState>(split_always);
    }
    Cluster::action_weak_fairness_is_stable(cluster.disable_req_drop());
    Cluster::action_weak_fairness_is_stable(cluster.disable_pod_monkey());
    stable_and_n!(
        always(lift_action(cluster.next())),
        tla_forall(|input| cluster.api_server_next().weak_fairness(input)),
        tla_forall(|input| cluster.builtin_controllers_next().weak_fairness(input)),
        tla_forall(|input: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, input.0, input.1))),
        tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness((controller_id, input))),
        tla_forall(|input| cluster.external_next().weak_fairness((controller_id, input))),
        cluster.disable_crash().weak_fairness(controller_id),
        cluster.disable_req_drop().weak_fairness(()),
        cluster.disable_pod_monkey().weak_fairness(())
    );
}

pub open spec fn vsts_cluster_invariants(
    vsts: VStatefulSetView, cluster: Cluster, controller_id: int
) -> StatePred<ClusterState> {
    // General cluster invariants
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
    Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id),
    Cluster::no_pending_request_to_api_server_from_non_controllers(),
    Cluster::desired_state_is(vsts),
    Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vsts.object_ref()),
    guarantee::vsts_internal_guarantee_conditions(controller_id)
    // vsts_rely_conditions(cluster, controller_id),
    )
    // .and(always(lift_state(helper_invariants::all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_labels(vsts))))
    // .and(always(lift_state(guarantee::every_msg_from_vsts_controller_carries_vsts_key(controller_id))))
    // .and(always(lift_state(garbage_collector_does_not_delete_vsts_pod_objects(vsts))))
}

// Pending request invariants for all reconcile states
pub open spec fn pending_request_invariants(cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![Init]))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).done)))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).error)))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreateNeeded])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![UpdateNeeded])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterListPod])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated])))))
}

pub proof fn pending_request_invariants_is_stable(cluster: Cluster, controller_id: int)
    ensures valid(stable(pending_request_invariants(cluster, controller_id))),
{
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![Init]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).done))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).error))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreateNeeded]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![UpdateNeeded]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterListPod]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated]))));
    stable_and_n!(
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![Init])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).done)))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).error)))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreateNeeded])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![UpdateNeeded])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterListPod])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated]))))
    );
}

pub open spec fn derived_invariants_since_beginning(vsts: VStatefulSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id())))
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
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref())))))
    .and(always(lift_state(Cluster::there_is_the_controller_state(controller_id))))
    .and(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))))
    .and(always(lift_state(Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![Init])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).done)))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).error)))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreateNeeded])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![UpdateNeeded])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterListPod])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned])))))
    .and(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated])))))
    .and(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id))))
}

pub proof fn derived_invariants_since_beginning_is_stable(vsts: VStatefulSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(derived_invariants_since_beginning(vsts, cluster, controller_id))),
{
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_has_unique_id()));
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()));
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()));
    always_p_is_stable(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)));
    always_p_is_stable(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()));
    always_p_is_stable(lift_state(Cluster::etcd_objects_have_unique_uids()));
    always_p_is_stable(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()));
    always_p_is_stable(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()));
    always_p_is_stable(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)));
    always_p_is_stable(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()));
    always_p_is_stable(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()));
    always_p_is_stable(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(controller_id)));
    always_p_is_stable(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)));
    always_p_is_stable(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)));
    always_p_is_stable(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)));
    always_p_is_stable(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)));
    always_p_is_stable(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VStatefulSetView>(controller_id)));
    always_p_is_stable(lift_state(Cluster::etcd_is_finite()));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref()))));
    always_p_is_stable(lift_state(Cluster::there_is_the_controller_state(controller_id)));
    always_p_is_stable(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)));
    always_p_is_stable(lift_state(Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id)));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![Init]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).done))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).error))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreateNeeded]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![UpdateNeeded]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterListPod]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned]))));
    always_p_is_stable(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated]))));
    always_p_is_stable(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)));
    stable_and_n!(
        always(lift_state(Cluster::every_in_flight_msg_has_unique_id())),
        always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())),
        always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))),
        always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id())),
        always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())),
        always(lift_state(Cluster::etcd_objects_have_unique_uids())),
        always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())),
        always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>())),
        always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id))),
        always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())),
        always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())),
        always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(controller_id))),
        always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))),
        always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))),
        always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))),
        always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id))),
        always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VStatefulSetView>(controller_id))),
        always(lift_state(Cluster::etcd_is_finite())),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref())))),
        always(lift_state(Cluster::there_is_the_controller_state(controller_id))),
        always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))),
        always(lift_state(Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![Init])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).done)))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).error)))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreateNeeded])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![UpdateNeeded])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterListPod])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned])))),
        always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated])))),
        always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))
    );
}

// The invariants that hold throughout the execution (next + weak fairness + derived invariants)
pub open spec fn invariants(vsts: VStatefulSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    next_with_wf(cluster, controller_id).and(derived_invariants_since_beginning(vsts, cluster, controller_id))
}

pub proof fn invariants_is_stable(vsts: VStatefulSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants(vsts, cluster, controller_id))),
{
    next_with_wf_is_stable(cluster, controller_id);
    derived_invariants_since_beginning_is_stable(vsts, cluster, controller_id);
    stable_and_n!(
        next_with_wf(cluster, controller_id),
        derived_invariants_since_beginning(vsts, cluster, controller_id)
    );
}

// Phase I: crash, req_drop, and pod_monkey disabled
pub open spec fn invariants_since_phase_i(controller_id: int, vsts: VStatefulSetView) -> TempPred<ClusterState> {
    always(lift_state(Cluster::crash_disabled(controller_id)))
    .and(always(lift_state(Cluster::req_drop_disabled())))
    .and(always(lift_state(Cluster::pod_monkey_disabled())))
}

pub proof fn invariants_since_phase_i_is_stable(controller_id: int, vsts: VStatefulSetView)
    ensures valid(stable(invariants_since_phase_i(controller_id, vsts))),
{
    stable_and_always_n!(
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled())
    );
}

// Phase II: no pending requests from non-controllers and pending req in flight xor resp in flight
pub open spec fn invariants_since_phase_ii(controller_id: int, vsts: VStatefulSetView) -> TempPred<ClusterState>
{
    always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()))
    .and(always(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, vsts.object_ref()))))
}

pub proof fn invariants_since_phase_ii_is_stable(controller_id: int, vsts: VStatefulSetView)
    ensures valid(stable(invariants_since_phase_ii(controller_id, vsts))),
{
    stable_and_always_n!(
        lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()),
        lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, vsts.object_ref()))
    );
}

// Phase III: every msg from key is pending req msg
pub open spec fn invariants_since_phase_iii(vsts: VStatefulSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vsts.object_ref())))
}

pub proof fn invariants_since_phase_iii_is_stable(vsts: VStatefulSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants_since_phase_iii(vsts, cluster, controller_id))),
{
    always_p_is_stable(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vsts.object_ref())));
}

// The combination of invariants and all phases
pub open spec fn assumption_and_invariants_of_all_phases(vsts: VStatefulSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    invariants(vsts, cluster, controller_id)
    .and(always(lift_state(Cluster::desired_state_is(vsts))))
    .and(invariants_since_phase_i(controller_id, vsts))
    .and(invariants_since_phase_ii(controller_id, vsts))
    .and(invariants_since_phase_iii(vsts, cluster, controller_id))
}

pub proof fn assumption_and_invariants_of_all_phases_is_stable(vsts: VStatefulSetView, cluster: Cluster, controller_id: int)
    ensures
        valid(stable(assumption_and_invariants_of_all_phases(vsts, cluster, controller_id))),
        valid(stable(invariants(vsts, cluster, controller_id))),
        forall |i: nat| 0 <= i <= 3 ==> valid(stable(#[trigger] spec_before_phase_n(i, vsts, cluster, controller_id))),
{
    reveal_with_fuel(spec_before_phase_n, 3);
    invariants_is_stable(vsts, cluster, controller_id);
    always_p_is_stable(lift_state(Cluster::desired_state_is(vsts)));
    invariants_since_phase_i_is_stable(controller_id, vsts);
    invariants_since_phase_ii_is_stable(controller_id, vsts);
    invariants_since_phase_iii_is_stable(vsts, cluster, controller_id);
    always_p_is_stable(lifted_vsts_rely_condition(cluster, controller_id));
    stable_and_n!(
        invariants(vsts, cluster, controller_id),
        always(lift_state(Cluster::desired_state_is(vsts))),
        invariants_since_phase_i(controller_id, vsts),
        invariants_since_phase_ii(controller_id, vsts),
        invariants_since_phase_iii(vsts, cluster, controller_id),
        always(lifted_vsts_rely_condition(cluster, controller_id))
    );
}

pub open spec fn invariants_since_phase_n(n: nat, vsts: VStatefulSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    if n == 0 {
        invariants(vsts, cluster, controller_id)
        .and(always(lift_state(Cluster::desired_state_is(vsts))))
    } else if n == 1 {
        invariants_since_phase_i(controller_id, vsts)
    } else if n == 2 {
        invariants_since_phase_ii(controller_id, vsts)
    } else if n == 3 {
        invariants_since_phase_iii(vsts, cluster, controller_id)
    } else {
        true_pred()
    }
}

pub open spec fn spec_before_phase_n(n: nat, vsts: VStatefulSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
    decreases n,
{
    if n == 1 {
        invariants(vsts, cluster, controller_id).and(always(lift_state(Cluster::desired_state_is(vsts))))
    } else if 2 <= n <= 4 {
        spec_before_phase_n((n-1) as nat, vsts, cluster, controller_id).and(invariants_since_phase_n((n-1) as nat, vsts, cluster, controller_id))
    } else {
        true_pred()
    }
}

pub open spec fn stable_spec(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    next_with_wf(cluster, controller_id)
    .and(always(lifted_vsts_rely_condition(cluster, controller_id)))
}

pub proof fn stable_spec_is_stable(cluster: Cluster, controller_id: int)
    ensures valid(stable(stable_spec(cluster, controller_id))),
{
    next_with_wf_is_stable(cluster, controller_id);
    always_p_is_stable(lifted_vsts_rely_condition(cluster, controller_id));
    stable_and_n!(
        next_with_wf(cluster, controller_id),
        always(lifted_vsts_rely_condition(cluster, controller_id))
    );
}

}
