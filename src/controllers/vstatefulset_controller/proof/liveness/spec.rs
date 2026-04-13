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
    model::{
        install::*, reconciler::*
    },
    proof::{
        internal_rely_guarantee, helper_invariants, helper_lemmas::*, liveness::*, predicate::*
    },
    trusted::{
        liveness_theorem::*, rely_guarantee::*, spec_types::*, step::VStatefulSetReconcileStepView::*,
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

// Pending request invariants for all reconcile states
pub open spec fn pending_request_invariants(cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![Init])))
    .and(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).done))))
    .and(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).error))))
    .and(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC]))))
    .and(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC]))))
    .and(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC]))))
    .and(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreateNeeded]))))
    .and(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![UpdateNeeded]))))
    .and(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned]))))
    .and(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated]))))
    .and(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterListPod]))))
    .and(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC]))))
    .and(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC]))))
    .and(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded]))))
    .and(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded]))))
    .and(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned]))))
    .and(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated]))))
}

pub proof fn spec_entails_pending_request_invariants_combine(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![Init]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).done))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).error))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreateNeeded]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![UpdateNeeded]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterListPod]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated]))))),
    ensures
        spec.entails(always(pending_request_invariants(cluster, controller_id))),
{
    
    let a_to_p_1  = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![Init])));
    let a_to_p_2  = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).done)));
    let a_to_p_3  = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).error)));
    let a_to_p_4  = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC])));
    let a_to_p_5  = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC])));
    let a_to_p_6  = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC])));
    let a_to_p_7  = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreateNeeded])));
    let a_to_p_8  = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![UpdateNeeded])));
    let a_to_p_9  = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned])));
    let a_to_p_10 = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated])));
    let a_to_p_11 = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterListPod])));
    let a_to_p_12 = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC])));
    let a_to_p_13 = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC])));
    let a_to_p_14 = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded])));
    let a_to_p_15 = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded])));
    let a_to_p_16 = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned])));
    let a_to_p_17 = tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated])));
    combine_spec_entails_always_n!(spec,
        pending_request_invariants(cluster, controller_id),
        a_to_p_1,
        a_to_p_2,
        a_to_p_3,
        a_to_p_4,
        a_to_p_5,
        a_to_p_6,
        a_to_p_7,
        a_to_p_8,
        a_to_p_9,
        a_to_p_10,
        a_to_p_11,
        a_to_p_12,
        a_to_p_13,
        a_to_p_14,
        a_to_p_15,
        a_to_p_16,
        a_to_p_17
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
    .and(always(pending_request_invariants(cluster, controller_id)))
    .and(always(lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id))))
    // Additional invariants needed by cluster_invariants_since_reconciliation
    .and(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())))
    .and(always(lift_state(helper_invariants::all_pvcs_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_or_owner_ref())))
    .and(always(lift_state(helper_invariants::buildin_controllers_do_not_delete_pvcs_owned_by_vsts())))
    .and(always(lift_state(helper_invariants::every_msg_from_vsts_controller_carries_vsts_key(controller_id))))
    .and(always(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<VStatefulSetView>(controller_id))))
    .and(always(lift_state(helper_invariants::all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts))))
}

pub proof fn spec_entails_derived_invariants_combine(spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int)
    requires
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(Cluster::etcd_objects_have_unique_uids()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))),
        spec.entails(always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VStatefulSetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref()))))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id)))),
        spec.entails(always(pending_request_invariants(cluster, controller_id))),
        spec.entails(always(lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)))),
        spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
        spec.entails(always(lift_state(helper_invariants::all_pvcs_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_or_owner_ref()))),
        spec.entails(always(lift_state(helper_invariants::buildin_controllers_do_not_delete_pvcs_owned_by_vsts()))),
        spec.entails(always(lift_state(helper_invariants::every_msg_from_vsts_controller_carries_vsts_key(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<VStatefulSetView>(controller_id)))),
        spec.entails(always(lift_state(helper_invariants::all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)))),
    ensures
        spec.entails(derived_invariants_since_beginning(vsts, cluster, controller_id)),
{
    let a_to_p = |vsts: VStatefulSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref()));
    entails_and_n!(spec,
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
        always(tla_forall(a_to_p)),
        always(lift_state(Cluster::there_is_the_controller_state(controller_id))),
        always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))),
        always(lift_state(Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id))),
        always(pending_request_invariants(cluster, controller_id)),
        always(lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id))),
        always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())),
        always(lift_state(helper_invariants::all_pvcs_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_or_owner_ref())),
        always(lift_state(helper_invariants::buildin_controllers_do_not_delete_pvcs_owned_by_vsts())),
        always(lift_state(helper_invariants::every_msg_from_vsts_controller_carries_vsts_key(controller_id))),
        always(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<VStatefulSetView>(controller_id))),
        always(lift_state(helper_invariants::all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)))
    );
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
    always_p_is_stable(pending_request_invariants(cluster, controller_id));
    always_p_is_stable(lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)));
    always_p_is_stable(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()));
    always_p_is_stable(lift_state(helper_invariants::all_pvcs_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_or_owner_ref()));
    always_p_is_stable(lift_state(helper_invariants::buildin_controllers_do_not_delete_pvcs_owned_by_vsts()));
    always_p_is_stable(lift_state(helper_invariants::every_msg_from_vsts_controller_carries_vsts_key(controller_id)));
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<VStatefulSetView>(controller_id)));
    always_p_is_stable(lift_state(helper_invariants::all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)));
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
        always(pending_request_invariants(cluster, controller_id)),
        always(lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id))),
        always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())),
        always(lift_state(helper_invariants::all_pvcs_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_or_owner_ref())),
        always(lift_state(helper_invariants::buildin_controllers_do_not_delete_pvcs_owned_by_vsts())),
        always(lift_state(helper_invariants::every_msg_from_vsts_controller_carries_vsts_key(controller_id))),
        always(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<VStatefulSetView>(controller_id))),
        always(lift_state(helper_invariants::all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)))
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

// Phase I: crash, req_drop, pod_monkey disabled, and the_object_in_schedule_has_spec_and_uid_as
pub open spec fn invariants_since_phase_i(controller_id: int, vsts: VStatefulSetView) -> TempPred<ClusterState> {
    always(lift_state(Cluster::crash_disabled(controller_id)))
    .and(always(lift_state(Cluster::req_drop_disabled())))
    .and(always(lift_state(Cluster::pod_monkey_disabled())))
    .and(always(lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, vsts))))
}

pub proof fn invariants_since_phase_i_is_stable(controller_id: int, vsts: VStatefulSetView)
    ensures valid(stable(invariants_since_phase_i(controller_id, vsts))),
{
    stable_and_always_n!(
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, vsts))
    );
}

// Phase II: reconcile_has_spec, no pending requests from non-controllers, pending req xor, reconcile_has_name_namespace
pub open spec fn invariants_since_phase_ii(controller_id: int, vsts: VStatefulSetView) -> TempPred<ClusterState>
{
    always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)))
    .and(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers())))
    .and(always(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, vsts.object_ref()))))
    .and(always(lift_state(helper_invariants::vsts_in_reconciles_has_the_same_name_and_namespace_as_vsts(vsts, controller_id))))
}

pub proof fn invariants_since_phase_ii_is_stable(controller_id: int, vsts: VStatefulSetView)
    ensures valid(stable(invariants_since_phase_ii(controller_id, vsts))),
{
    stable_and_always_n!(
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)),
        lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()),
        lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, vsts.object_ref())),
        lift_state(helper_invariants::vsts_in_reconciles_has_the_same_name_and_namespace_as_vsts(vsts, controller_id))
    );
}

// Phase III: every msg from key is pending req msg, all pod requests carry correct owner ref
pub open spec fn invariants_since_phase_iii(vsts: VStatefulSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vsts.object_ref())))
    .and(always(lift_state(Cluster::every_in_flight_req_msg_satisfies(helper_invariants::all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id)))))
}

pub proof fn invariants_since_phase_iii_is_stable(vsts: VStatefulSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants_since_phase_iii(vsts, cluster, controller_id))),
{
    stable_and_always_n!(
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vsts.object_ref())),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(helper_invariants::all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id)))
    );
}

// Phase IV: builtin_controllers_do_not_delete_pods_owned_by_vsts and all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_no_deletion_timestamp
pub open spec fn invariants_since_phase_iv(vsts: VStatefulSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(helper_invariants::buildin_controllers_do_not_delete_pods_owned_by_vsts(vsts)))
    .and(always(lift_state(helper_invariants::all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_no_deletion_timestamp(vsts))))
}

pub proof fn invariants_since_phase_iv_is_stable(vsts: VStatefulSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants_since_phase_iv(vsts, cluster, controller_id))),
{
    stable_and_always_n!(
        lift_state(helper_invariants::buildin_controllers_do_not_delete_pods_owned_by_vsts(vsts)),
        lift_state(helper_invariants::all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_no_deletion_timestamp(vsts))
    );
}

// The combination of invariants and all phases
pub open spec fn assumption_and_invariants_of_all_phases(vsts: VStatefulSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    invariants(vsts, cluster, controller_id)
    .and(always(lift_state(Cluster::desired_state_is(vsts))))
    .and(invariants_since_phase_i(controller_id, vsts))
    .and(invariants_since_phase_ii(controller_id, vsts))
    .and(invariants_since_phase_iii(vsts, cluster, controller_id))
    .and(invariants_since_phase_iv(vsts, cluster, controller_id))
}

pub proof fn assumption_and_invariants_of_all_phases_is_stable(vsts: VStatefulSetView, cluster: Cluster, controller_id: int)
    ensures
        valid(stable(assumption_and_invariants_of_all_phases(vsts, cluster, controller_id))),
        valid(stable(invariants(vsts, cluster, controller_id))),
        forall |i: nat| 0 <= i <= 4 ==> valid(stable(#[trigger] spec_before_phase_n(i, vsts, cluster, controller_id))),
{
    reveal_with_fuel(spec_before_phase_n, 4);
    invariants_is_stable(vsts, cluster, controller_id);
    always_p_is_stable(lift_state(Cluster::desired_state_is(vsts)));
    invariants_since_phase_i_is_stable(controller_id, vsts);
    invariants_since_phase_ii_is_stable(controller_id, vsts);
    invariants_since_phase_iii_is_stable(vsts, cluster, controller_id);
    invariants_since_phase_iv_is_stable(vsts, cluster, controller_id);
    stable_and_n!(
        invariants(vsts, cluster, controller_id),
        always(lift_state(Cluster::desired_state_is(vsts))),
        invariants_since_phase_i(controller_id, vsts),
        invariants_since_phase_ii(controller_id, vsts),
        invariants_since_phase_iii(vsts, cluster, controller_id),
        invariants_since_phase_iv(vsts, cluster, controller_id)
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
    } else if n == 4 {
        invariants_since_phase_iv(vsts, cluster, controller_id)
    } else {
        true_pred()
    }
}

pub open spec fn spec_before_phase_n(n: nat, vsts: VStatefulSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
    decreases n,
{
    if n == 1 {
        invariants(vsts, cluster, controller_id).and(always(lift_state(Cluster::desired_state_is(vsts))))
    } else if 2 <= n <= 5 {
        spec_before_phase_n((n-1) as nat, vsts, cluster, controller_id).and(invariants_since_phase_n((n-1) as nat, vsts, cluster, controller_id))
    } else {
        true_pred()
    }
}

pub open spec fn stable_spec(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    next_with_wf(cluster, controller_id)
}

pub proof fn stable_spec_is_stable(cluster: Cluster, controller_id: int)
    ensures valid(stable(stable_spec(cluster, controller_id))),
{
    next_with_wf_is_stable(cluster, controller_id);
}

}
