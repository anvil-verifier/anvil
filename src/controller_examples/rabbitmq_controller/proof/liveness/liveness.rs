// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::{built_in_controller_req_msg, BuiltinControllerChoice},
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    common::*,
    proof::{common::*, liveness::helper_invariants, terminate},
    spec::{rabbitmqcluster::*, reconciler::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// The current state matches the desired state described in the cr.
// I.e., the corresponding stateful set exists and its spec is the same as desired.
spec fn current_config_map_matches(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).is_Ok()
        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).get_Ok_0().data == make_server_config_map(rabbitmq).data
    }
}

// The liveness property says []desired_state_is(rabbitmq) ~> []current_config_map_matches(rabbitmq).
spec fn liveness(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster>
    recommends
        rabbitmq.well_formed(),
{
    always(lift_state(RMQCluster::desired_state_is(rabbitmq))).leads_to(always(lift_state(current_config_map_matches(rabbitmq))))
}

// We prove init /\ []next /\ []wf |= []RMQCluster::desired_state_is(rabbitmq) ~> []current_config_map_matches(rabbitmq) holds for each rabbitmq.
proof fn liveness_proof_forall_rabbitmq()
    ensures
        forall |rabbitmq: RabbitmqClusterView| rabbitmq.well_formed() ==> #[trigger] cluster_spec().entails(liveness(rabbitmq)),
{
    assert forall |rabbitmq: RabbitmqClusterView| rabbitmq.well_formed()
    implies #[trigger] cluster_spec().entails(liveness(rabbitmq)) by {
        liveness_proof(rabbitmq);
    };
}

// Next and all the wf conditions.
spec fn next_with_wf() -> TempPred<RMQCluster> {
    always(lift_action(RMQCluster::next()))
    .and(tla_forall(|input| RMQCluster::kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::controller_next().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::schedule_controller_reconcile().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::builtin_controllers_next().weak_fairness(input)))
    .and(RMQCluster::disable_crash().weak_fairness(()))
    .and(RMQCluster::disable_busy().weak_fairness(()))
}

proof fn next_with_wf_is_stable()
    ensures
        valid(stable(next_with_wf())),
{
    always_p_is_stable(lift_action(RMQCluster::next()));
    RMQCluster::tla_forall_action_weak_fairness_is_stable(RMQCluster::kubernetes_api_next());
    RMQCluster::tla_forall_action_weak_fairness_is_stable(RMQCluster::controller_next());
    RMQCluster::tla_forall_action_weak_fairness_is_stable(RMQCluster::schedule_controller_reconcile());
    RMQCluster::tla_forall_action_weak_fairness_is_stable(RMQCluster::builtin_controllers_next());
    RMQCluster::action_weak_fairness_is_stable(RMQCluster::disable_crash());
    RMQCluster::action_weak_fairness_is_stable(RMQCluster::disable_busy());
    stable_and_n!(
        always(lift_action(RMQCluster::next())),
        tla_forall(|input| RMQCluster::kubernetes_api_next().weak_fairness(input)),
        tla_forall(|input| RMQCluster::controller_next().weak_fairness(input)),
        tla_forall(|input| RMQCluster::schedule_controller_reconcile().weak_fairness(input)),
        tla_forall(|input| RMQCluster::builtin_controllers_next().weak_fairness(input)),
        RMQCluster::disable_crash().weak_fairness(()),
        RMQCluster::disable_busy().weak_fairness(())
    );
}

spec fn next_with_wf_and_assumption(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(lift_action(RMQCluster::next()))
    .and(tla_forall(|input| RMQCluster::kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::controller_next().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::schedule_controller_reconcile().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::builtin_controllers_next().weak_fairness(input)))
    .and(RMQCluster::disable_crash().weak_fairness(()))
    .and(RMQCluster::disable_busy().weak_fairness(()))
    .and(always(lift_state(RMQCluster::desired_state_is(rabbitmq))))
}

spec fn next_with_wf_and_assumption_and_all_invariants(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(lift_action(RMQCluster::next()))
    .and(tla_forall(|input| RMQCluster::kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::controller_next().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::schedule_controller_reconcile().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::builtin_controllers_next().weak_fairness(input)))
    .and(RMQCluster::disable_crash().weak_fairness(()))
    .and(RMQCluster::disable_busy().weak_fairness(()))
    .and(always(lift_state(RMQCluster::desired_state_is(rabbitmq))))
    .and(invariants_phase_I(rabbitmq))
    .and(invariants_phase_II(rabbitmq))
    .and(invariants_phase_III(rabbitmq))
    .and(invariants_phase_IV(rabbitmq))
    .and(invariants_phase_V(rabbitmq))
    .and(invariants_phase_VI(rabbitmq))
}

proof fn next_with_wf_and_assumption_is_stable(rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(next_with_wf_and_assumption(rabbitmq))),
{
    always_p_is_stable(lift_state(RMQCluster::desired_state_is(rabbitmq)));
    next_with_wf_is_stable();
    stable_and_temp(
        next_with_wf(),
        always(lift_state(RMQCluster::desired_state_is(rabbitmq)))
    );
}

// The safety invariants that are required to prove liveness.
spec fn invariants_phase_I(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref()))))
    .and(always(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref()))))
    .and(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed())))
    .and(always(lift_state(RMQCluster::each_scheduled_key_is_consistent_with_its_object())))
    .and(always(lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object())))
    .and(always(lift_state(helper_invariants::stateful_set_only_has_controller_owner_ref(rabbitmq))))
    .and(always(lift_state(helper_invariants::pending_msg_at_after_create_server_config_map_step_is_create_cm_req(rabbitmq.object_ref()))))
    .and(always(lift_state(helper_invariants::pending_msg_at_after_update_server_config_map_step_is_update_cm_req(rabbitmq.object_ref()))))
    .and(always(lift_state(helper_invariants::pending_msg_at_after_create_stateful_set_step_is_create_sts_req(rabbitmq.object_ref()))))
    .and(always(lift_state(helper_invariants::pending_msg_at_after_update_stateful_set_step_is_update_sts_req(rabbitmq.object_ref()))))
    .and(always(lift_state(RMQCluster::no_pending_req_msg_or_external_api_input_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::Init)))))
    .and(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateHeadlessService)))))
    .and(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateService)))))
    .and(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateErlangCookieSecret)))))
    .and(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateDefaultUserSecret)))))
    .and(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreatePluginsConfigMap)))))
    .and(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterGetServerConfigMap)))))
    .and(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateServerConfigMap)))))
    .and(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterUpdateServerConfigMap)))))
    .and(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateServiceAccount)))))
    .and(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateRole)))))
    .and(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateRoleBinding)))))
    .and(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterGetStatefulSet)))))
    .and(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateStatefulSet)))))
    .and(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterUpdateStatefulSet)))))
}

proof fn invariants_is_stable(rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(invariants_phase_I(rabbitmq))),
{
    stable_and_always_n!(
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())),
        lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(RMQCluster::each_scheduled_key_is_consistent_with_its_object()),
        lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()),
        lift_state(helper_invariants::stateful_set_only_has_controller_owner_ref(rabbitmq)),
        lift_state(helper_invariants::pending_msg_at_after_create_server_config_map_step_is_create_cm_req(rabbitmq.object_ref())),
        lift_state(helper_invariants::pending_msg_at_after_update_server_config_map_step_is_update_cm_req(rabbitmq.object_ref())),
        lift_state(helper_invariants::pending_msg_at_after_create_stateful_set_step_is_create_sts_req(rabbitmq.object_ref())),
        lift_state(helper_invariants::pending_msg_at_after_update_stateful_set_step_is_update_sts_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::no_pending_req_msg_or_external_api_input_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::Init))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateHeadlessService))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateService))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateErlangCookieSecret))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateDefaultUserSecret))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreatePluginsConfigMap))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterGetServerConfigMap))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateServerConfigMap))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterUpdateServerConfigMap))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateServiceAccount))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateRole))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateRoleBinding))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterGetStatefulSet))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateStatefulSet))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterUpdateStatefulSet)))
    );
}

spec fn invariants_phase_II(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(lift_state(RMQCluster::crash_disabled()))
    .and(always(lift_state(RMQCluster::busy_disabled())))
}

spec fn invariants_phase_III(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(lift_state(RMQCluster::the_object_in_schedule_has_spec_and_uid_as(rabbitmq)))
    .and(always(lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq))))
}

// TODO: move desired_state_is(rabbitmq) from phase II
proof fn invariants_phase_II_is_stable(rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(invariants_phase_II(rabbitmq))),
{
    stable_and_always_n!(
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled())
    );
}

proof fn invariants_phase_III_is_stable(rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(invariants_phase_III(rabbitmq))),
{
    stable_and_always_n!(
        lift_state(RMQCluster::the_object_in_schedule_has_spec_and_uid_as(rabbitmq)),
        lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq))
    );
}

// Some other invariants requires to prove liveness.
// Note that different from the above invariants, these do not hold for the entire execution from init.
// They only hold since some point (e.g., when the rest id counter is the same as rest_id).
// Some of these invariants are also based on the assumptions.
spec fn invariants_phase_IV(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(lift_state(helper_invariants::at_most_one_create_cm_req_is_in_flight(rabbitmq.object_ref())))
    .and(always(lift_state(helper_invariants::at_most_one_update_cm_req_is_in_flight(rabbitmq.object_ref()))))
    .and(always(lift_state(helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref()))))
    .and(always(lift_state(helper_invariants::every_update_cm_req_does_the_same(rabbitmq))))
    .and(always(lift_state(helper_invariants::at_most_one_create_sts_req_is_in_flight(rabbitmq.object_ref()))))
    .and(always(lift_state(helper_invariants::at_most_one_update_sts_req_is_in_flight(rabbitmq.object_ref()))))
    .and(always(lift_state(helper_invariants::every_update_sts_req_does_the_same(rabbitmq))))
    .and(always(lift_state(helper_invariants::every_create_sts_req_does_the_same(rabbitmq))))
}

proof fn invariants_phase_IV_is_stable(rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(invariants_phase_IV(rabbitmq))),
{
    stable_and_always_n!(
        lift_state(helper_invariants::at_most_one_create_cm_req_is_in_flight(rabbitmq.object_ref())),
        lift_state(helper_invariants::at_most_one_update_cm_req_is_in_flight(rabbitmq.object_ref())),
        lift_state(helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref())),
        lift_state(helper_invariants::every_update_cm_req_does_the_same(rabbitmq)),
        lift_state(helper_invariants::at_most_one_create_sts_req_is_in_flight(rabbitmq.object_ref())),
        lift_state(helper_invariants::at_most_one_update_sts_req_is_in_flight(rabbitmq.object_ref())),
        lift_state(helper_invariants::every_update_sts_req_does_the_same(rabbitmq)),
        lift_state(helper_invariants::every_create_sts_req_does_the_same(rabbitmq))
    );
}

// This invariant is also used to prove liveness.
// Different from above, it only holds after some time since the rest id counter is the same as rest_id.
spec fn invariants_phase_V(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(lift_state(helper_invariants::stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq)))
}

proof fn invariants_phase_V_is_stable(rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(invariants_phase_V(rabbitmq))),
{
    always_p_is_stable(lift_state(helper_invariants::stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq)));
}

spec fn invariants_phase_VI(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(lift_state(helper_invariants::no_delete_sts_req_is_in_flight(rabbitmq.object_ref())))
}

proof fn invariants_phase_VI_is_stable(rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(invariants_phase_VI(rabbitmq))),
{
    always_p_is_stable(lift_state(helper_invariants::no_delete_sts_req_is_in_flight(rabbitmq.object_ref())));
}

proof fn liveness_proof(rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
    ensures
        cluster_spec().entails(liveness(rabbitmq)),
{
    lemma_true_leads_to_always_current_state_matches_rabbitmq_under_eventual_invariants(rabbitmq);

    next_with_wf_is_stable();
    next_with_wf_and_assumption_is_stable(rabbitmq);
    invariants_is_stable(rabbitmq);
    invariants_phase_II_is_stable(rabbitmq);
    invariants_phase_III_is_stable(rabbitmq);
    invariants_phase_IV_is_stable(rabbitmq);
    invariants_phase_V_is_stable(rabbitmq);
    // Eliminate all the invariants by phase.
    assert_by(
        next_with_wf_and_assumption(rabbitmq).and(invariants_phase_I(rabbitmq)).and(invariants_phase_II(rabbitmq)).and(invariants_phase_III(rabbitmq)).and(invariants_phase_IV(rabbitmq)).and(invariants_phase_V(rabbitmq)).entails(
            true_pred().leads_to(always(lift_state(current_config_map_matches(rabbitmq))))
        ),
        {
            let spec = next_with_wf_and_assumption(rabbitmq).and(invariants_phase_I(rabbitmq)).and(invariants_phase_II(rabbitmq)).and(invariants_phase_III(rabbitmq)).and(invariants_phase_IV(rabbitmq)).and(invariants_phase_V(rabbitmq));
            stable_and_n!(
                next_with_wf_and_assumption(rabbitmq),
                invariants_phase_I(rabbitmq),
                invariants_phase_II(rabbitmq),
                invariants_phase_III(rabbitmq),
                invariants_phase_IV(rabbitmq),
                invariants_phase_V(rabbitmq)
            );
            unpack_conditions_from_spec(spec, invariants_phase_VI(rabbitmq), true_pred(), always(lift_state(current_config_map_matches(rabbitmq))));
            temp_pred_equality(true_pred().and(invariants_phase_VI(rabbitmq)), invariants_phase_VI(rabbitmq));
            eliminate_always(spec, lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()));
            helper_invariants::lemma_true_leads_to_always_no_delete_sts_req_is_in_flight(spec, rabbitmq.object_ref());
            leads_to_trans_temp(spec, true_pred(), invariants_phase_VI(rabbitmq), always(lift_state(current_config_map_matches(rabbitmq))));
        }
    );
    assert_by(
        next_with_wf_and_assumption(rabbitmq).and(invariants_phase_I(rabbitmq)).and(invariants_phase_II(rabbitmq)).and(invariants_phase_III(rabbitmq)).and(invariants_phase_IV(rabbitmq)).entails(
            true_pred().leads_to(always(lift_state(current_config_map_matches(rabbitmq))))
        ),
        {
            let spec = next_with_wf_and_assumption(rabbitmq).and(invariants_phase_I(rabbitmq)).and(invariants_phase_II(rabbitmq)).and(invariants_phase_III(rabbitmq)).and(invariants_phase_IV(rabbitmq));
            stable_and_n!(
                next_with_wf_and_assumption(rabbitmq),
                invariants_phase_I(rabbitmq),
                invariants_phase_II(rabbitmq),
                invariants_phase_III(rabbitmq),
                invariants_phase_IV(rabbitmq)
            );
            unpack_conditions_from_spec(spec, invariants_phase_V(rabbitmq), true_pred(), always(lift_state(current_config_map_matches(rabbitmq))));
            temp_pred_equality(true_pred().and(invariants_phase_V(rabbitmq)), always(lift_state(helper_invariants::stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq))));
            lemma_eventually_only_valid_stateful_set_exists(spec, rabbitmq);
            leads_to_trans_temp(spec, true_pred(), invariants_phase_V(rabbitmq), always(lift_state(current_config_map_matches(rabbitmq))));
        }
    );
    assert_by(
        next_with_wf_and_assumption(rabbitmq).and(invariants_phase_I(rabbitmq)).and(invariants_phase_II(rabbitmq)).and(invariants_phase_III(rabbitmq)).entails(
            true_pred().leads_to(always(lift_state(current_config_map_matches(rabbitmq))))
        ),
        {
            let spec = next_with_wf_and_assumption(rabbitmq).and(invariants_phase_I(rabbitmq)).and(invariants_phase_II(rabbitmq)).and(invariants_phase_III(rabbitmq));
            stable_and_n!(
                next_with_wf_and_assumption(rabbitmq),
                invariants_phase_I(rabbitmq),
                invariants_phase_II(rabbitmq),
                invariants_phase_III(rabbitmq)
            );
            unpack_conditions_from_spec(spec, invariants_phase_IV(rabbitmq), true_pred(), always(lift_state(current_config_map_matches(rabbitmq))));
            temp_pred_equality(true_pred().and(invariants_phase_IV(rabbitmq)), invariants_phase_IV(rabbitmq));
            
            eliminate_always(spec, lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()));
            eliminate_always(spec, lift_state(helper_invariants::pending_msg_at_after_create_server_config_map_step_is_create_cm_req(rabbitmq.object_ref())));
            eliminate_always(spec, lift_state(helper_invariants::pending_msg_at_after_update_server_config_map_step_is_update_cm_req(rabbitmq.object_ref())));
            eliminate_always(spec, lift_state(helper_invariants::pending_msg_at_after_create_stateful_set_step_is_create_sts_req(rabbitmq.object_ref())));
            eliminate_always(spec, lift_state(helper_invariants::pending_msg_at_after_update_stateful_set_step_is_update_sts_req(rabbitmq.object_ref())));

            helper_invariants::lemma_true_leads_to_always_at_most_one_create_cm_req_is_in_flight(spec, rabbitmq.object_ref());
            helper_invariants::lemma_true_leads_to_always_at_most_one_update_cm_req_is_in_flight(spec, rabbitmq.object_ref());
            helper_invariants::lemma_true_leads_to_always_no_delete_cm_req_is_in_flight(spec, rabbitmq.object_ref());
            helper_invariants::lemma_true_leads_to_always_every_update_cm_req_does_the_same(spec, rabbitmq);
            helper_invariants::lemma_true_leads_to_always_at_most_one_create_sts_req_is_in_flight(spec, rabbitmq.object_ref());
            helper_invariants::lemma_true_leads_to_always_at_most_one_update_sts_req_is_in_flight(spec, rabbitmq.object_ref());
            helper_invariants::lemma_true_leads_to_always_every_update_sts_req_does_the_same(spec, rabbitmq);
            helper_invariants::lemma_true_leads_to_always_every_create_sts_req_does_the_same(spec, rabbitmq);

            leads_to_always_combine_n!(
                spec, true_pred(),
                lift_state(helper_invariants::at_most_one_create_cm_req_is_in_flight(rabbitmq.object_ref())),
                lift_state(helper_invariants::at_most_one_update_cm_req_is_in_flight(rabbitmq.object_ref())),
                lift_state(helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref())),
                lift_state(helper_invariants::every_update_cm_req_does_the_same(rabbitmq)),
                lift_state(helper_invariants::at_most_one_create_sts_req_is_in_flight(rabbitmq.object_ref())),
                lift_state(helper_invariants::at_most_one_update_sts_req_is_in_flight(rabbitmq.object_ref())),
                lift_state(helper_invariants::every_update_sts_req_does_the_same(rabbitmq)),
                lift_state(helper_invariants::every_create_sts_req_does_the_same(rabbitmq))
            );

            always_and_equality_n!(
                lift_state(helper_invariants::at_most_one_create_cm_req_is_in_flight(rabbitmq.object_ref())),
                lift_state(helper_invariants::at_most_one_update_cm_req_is_in_flight(rabbitmq.object_ref())),
                lift_state(helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref())),
                lift_state(helper_invariants::every_update_cm_req_does_the_same(rabbitmq)),
                lift_state(helper_invariants::at_most_one_create_sts_req_is_in_flight(rabbitmq.object_ref())),
                lift_state(helper_invariants::at_most_one_update_sts_req_is_in_flight(rabbitmq.object_ref())),
                lift_state(helper_invariants::every_update_sts_req_does_the_same(rabbitmq)),
                lift_state(helper_invariants::every_create_sts_req_does_the_same(rabbitmq))
            );

            leads_to_trans_temp(spec, true_pred(), invariants_phase_IV(rabbitmq), always(lift_state(current_config_map_matches(rabbitmq))));
        }
    );
    assert_by(
        next_with_wf_and_assumption(rabbitmq).and(invariants_phase_I(rabbitmq)).and(invariants_phase_II(rabbitmq)).entails(
            true_pred().leads_to(always(lift_state(current_config_map_matches(rabbitmq))))
        ),
        {
            let spec = next_with_wf_and_assumption(rabbitmq).and(invariants_phase_I(rabbitmq)).and(invariants_phase_II(rabbitmq));
            stable_and_n!(
                next_with_wf_and_assumption(rabbitmq),
                invariants_phase_I(rabbitmq),
                invariants_phase_II(rabbitmq)
            );
            unpack_conditions_from_spec(spec, invariants_phase_III(rabbitmq), true_pred(), always(lift_state(current_config_map_matches(rabbitmq))));
            temp_pred_equality(true_pred().and(invariants_phase_III(rabbitmq)), invariants_phase_III(rabbitmq));

            terminate::reconcile_eventually_terminates(spec, rabbitmq);
            RMQCluster::lemma_true_leads_to_always_the_object_in_schedule_has_spec_and_uid_as(spec, rabbitmq);
            RMQCluster::lemma_true_leads_to_always_the_object_in_reconcile_has_spec_and_uid_as(spec, rabbitmq);

            leads_to_always_combine_n!(
                spec, true_pred(),
                lift_state(RMQCluster::the_object_in_schedule_has_spec_and_uid_as(rabbitmq)),
                lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq))
            );

            always_and_equality_n!(
                lift_state(RMQCluster::the_object_in_schedule_has_spec_and_uid_as(rabbitmq)),
                lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq))
            );

            leads_to_trans_temp(spec, true_pred(), invariants_phase_III(rabbitmq), always(lift_state(current_config_map_matches(rabbitmq))));
        }
    );

    // Now we eliminate the assumption []RMQCluster::crash_disabled() /\ []busy_disabled.
    assert_by(
        next_with_wf_and_assumption(rabbitmq).and(invariants_phase_I(rabbitmq))
        .entails(
            true_pred().leads_to(always(lift_state(current_config_map_matches(rabbitmq))))
        ),
        {
            let spec = next_with_wf_and_assumption(rabbitmq).and(invariants_phase_I(rabbitmq));
            stable_and_n!(
                next_with_wf_and_assumption(rabbitmq),
                invariants_phase_I(rabbitmq)
            );
            unpack_conditions_from_spec(spec, invariants_phase_II(rabbitmq), true_pred(), always(lift_state(current_config_map_matches(rabbitmq))));
            temp_pred_equality(true_pred().and(invariants_phase_II(rabbitmq)), invariants_phase_II(rabbitmq));

            RMQCluster::lemma_true_leads_to_crash_always_disabled(spec);
            RMQCluster::lemma_true_leads_to_busy_always_disabled(spec);
            leads_to_always_combine_temp(
                spec,
                true_pred(),
                lift_state(RMQCluster::crash_disabled()),
                lift_state(RMQCluster::busy_disabled())
            );
            always_and_equality(
                lift_state(RMQCluster::crash_disabled()),
                lift_state(RMQCluster::busy_disabled())
            );
            leads_to_trans_temp(spec, true_pred(), invariants_phase_II(rabbitmq), always(lift_state(current_config_map_matches(rabbitmq))));
        }
    );

    // Then we unpack the assumption of []RMQCluster::desired_state_is(rabbitmq) from spec.
    assert_by(
        next_with_wf().and(invariants_phase_I(rabbitmq))
        .entails(
            always(lift_state(RMQCluster::desired_state_is(rabbitmq))).leads_to(always(lift_state(current_config_map_matches(rabbitmq))))
        ),
        {
            let spec = next_with_wf().and(invariants_phase_I(rabbitmq));
            let assumption = always(lift_state(RMQCluster::desired_state_is(rabbitmq)));
            stable_and_n!(next_with_wf(), invariants_phase_I(rabbitmq));
            temp_pred_equality(spec.and(assumption), next_with_wf_and_assumption(rabbitmq).and(invariants_phase_I(rabbitmq)));
            unpack_conditions_from_spec(spec, assumption, true_pred(), always(lift_state(current_config_map_matches(rabbitmq))));
            temp_pred_equality(true_pred().and(assumption), assumption);
        }
    );

    entails_trans(
        cluster_spec().and(invariants_phase_I(rabbitmq)), next_with_wf().and(invariants_phase_I(rabbitmq)),
        always(lift_state(RMQCluster::desired_state_is(rabbitmq))).leads_to(always(lift_state(current_config_map_matches(rabbitmq))))
    );
    sm_spec_entails_all_invariants(rabbitmq);
    simplify_predicate(cluster_spec(), invariants_phase_I(rabbitmq));
}

proof fn sm_spec_entails_all_invariants(rabbitmq: RabbitmqClusterView)
    ensures
        cluster_spec().entails(invariants_phase_I(rabbitmq)),
{
    let spec = cluster_spec();
    RMQCluster::lemma_always_every_in_flight_msg_has_unique_id();
    RMQCluster::lemma_always_each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref());
    RMQCluster::lemma_always_each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref());
    RMQCluster::lemma_always_every_in_flight_msg_has_lower_id_than_allocator();
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    RMQCluster::lemma_always_each_scheduled_key_is_consistent_with_its_object(spec);
    RMQCluster::lemma_always_each_key_in_reconcile_is_consistent_with_its_object(spec);
    helper_invariants::lemma_always_stateful_set_only_has_controller_owner_ref(spec, rabbitmq);
    helper_invariants::lemma_always_pending_msg_at_after_create_server_config_map_step_is_create_cm_req(spec, rabbitmq.object_ref());
    helper_invariants::lemma_always_pending_msg_at_after_update_server_config_map_step_is_update_cm_req(spec, rabbitmq.object_ref());
    helper_invariants::lemma_always_pending_msg_at_after_create_stateful_set_step_is_create_sts_req(spec, rabbitmq.object_ref());
    helper_invariants::lemma_always_pending_msg_at_after_update_stateful_set_step_is_update_sts_req(spec, rabbitmq.object_ref());
    RMQCluster::lemma_always_no_pending_req_msg_or_external_api_input_at_reconcile_state(spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::Init));
    RMQCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateHeadlessService)
    );
    RMQCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateService)
    );
    RMQCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateErlangCookieSecret)
    );
    RMQCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateDefaultUserSecret)
    );
    RMQCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreatePluginsConfigMap)
    );
    RMQCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterGetServerConfigMap)
    );
    RMQCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateServerConfigMap)
    );
    RMQCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterUpdateServerConfigMap)
    );
    RMQCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateServiceAccount)
    );
    RMQCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateRole)
    );
    RMQCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateRoleBinding)
    );
    RMQCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterGetStatefulSet)
    );
    RMQCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateStatefulSet)
    );
    RMQCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterUpdateStatefulSet)
    );
    entails_always_and_n!(
        spec,
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())),
        lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(RMQCluster::each_scheduled_key_is_consistent_with_its_object()),
        lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()),
        lift_state(helper_invariants::stateful_set_only_has_controller_owner_ref(rabbitmq)),
        lift_state(helper_invariants::pending_msg_at_after_create_server_config_map_step_is_create_cm_req(rabbitmq.object_ref())),
        lift_state(helper_invariants::pending_msg_at_after_update_server_config_map_step_is_update_cm_req(rabbitmq.object_ref())),
        lift_state(helper_invariants::pending_msg_at_after_create_stateful_set_step_is_create_sts_req(rabbitmq.object_ref())),
        lift_state(helper_invariants::pending_msg_at_after_update_stateful_set_step_is_update_sts_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::no_pending_req_msg_or_external_api_input_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::Init))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateHeadlessService))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateService))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateErlangCookieSecret))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateDefaultUserSecret))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreatePluginsConfigMap))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterGetServerConfigMap))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateServerConfigMap))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterUpdateServerConfigMap))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateServiceAccount))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateRole))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateRoleBinding))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterGetStatefulSet))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterCreateStatefulSet))),
        lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterUpdateStatefulSet)))
    );
}

// This lemma proves that with all the invariants, assumptions, and even invariants that only hold since rest id counter is rest_id,
// true ~> []current_state_matches(rabbitmq).
proof fn lemma_true_leads_to_always_current_state_matches_rabbitmq_under_eventual_invariants(rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
    ensures
        next_with_wf_and_assumption_and_all_invariants(rabbitmq)
        .entails(
            true_pred().leads_to(always(lift_state(current_config_map_matches(rabbitmq))))
        ),
{
    let spec = next_with_wf_and_assumption_and_all_invariants(rabbitmq);

    // The use of termination property ensures spec |= true ~> reconcile_idle.
    terminate::reconcile_eventually_terminates(spec, rabbitmq);
    // Then we can continue to show that spec |= reconcile_idle ~> []current_state_matches(rabbitmq).

    // The following two lemmas show that spec |= reconcile_idle ~> init /\ no_pending_req.
    lemma_from_reconcile_idle_to_scheduled(spec, rabbitmq);
    lemma_from_scheduled_to_init_step(spec, rabbitmq);

    // After applying this lemma, we get spec |= init /\ no_pending_req ~> create_headless_service /\ pending_req.
    lemma_from_init_step_to_after_create_headless_service_step(spec, rabbitmq);

    lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, rabbitmq,
        RabbitmqReconcileStep::AfterCreateHeadlessService, RabbitmqReconcileStep::AfterCreateService);
    lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, rabbitmq,
        RabbitmqReconcileStep::AfterCreateService, RabbitmqReconcileStep::AfterCreateErlangCookieSecret);
    lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, rabbitmq,
        RabbitmqReconcileStep::AfterCreateErlangCookieSecret, RabbitmqReconcileStep::AfterCreateDefaultUserSecret);
    lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, rabbitmq,
        RabbitmqReconcileStep::AfterCreateDefaultUserSecret, RabbitmqReconcileStep::AfterCreatePluginsConfigMap);
    lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, rabbitmq,
        RabbitmqReconcileStep::AfterCreatePluginsConfigMap, RabbitmqReconcileStep::AfterGetServerConfigMap);

    // TODO: show that AfterGetServerConfigMap ~> AfterCreateServiceAccount
    lemma_from_after_get_server_config_map_to_rabbitmq_matches(rabbitmq);
    
    lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, rabbitmq, RabbitmqReconcileStep::AfterCreateServiceAccount, RabbitmqReconcileStep::AfterCreateRole);
    lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, rabbitmq, RabbitmqReconcileStep::AfterCreateRole, RabbitmqReconcileStep::AfterCreateRoleBinding);
    lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, rabbitmq, RabbitmqReconcileStep::AfterCreateRoleBinding, RabbitmqReconcileStep::AfterGetStatefulSet);

    leads_to_trans_n!(
        spec,
        true_pred(),
        lift_state(|s: RMQCluster| { !s.reconcile_state_contains(rabbitmq.object_ref()) }),
        lift_state(|s: RMQCluster| { !s.reconcile_state_contains(rabbitmq.object_ref()) && s.reconcile_scheduled_for(rabbitmq.object_ref())}),
        lift_state(no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateHeadlessService, rabbitmq)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateService, rabbitmq)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateErlangCookieSecret, rabbitmq)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateDefaultUserSecret, rabbitmq)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreatePluginsConfigMap, rabbitmq)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)),
        lift_state(current_config_map_matches(rabbitmq))
    );

    lemma_server_config_map_is_stable(spec, rabbitmq, lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)));
    leads_to_trans_temp(
        spec, true_pred(),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)),
        always(lift_state(current_config_map_matches(rabbitmq)))
    );
}

proof fn lemma_from_reconcile_idle_to_scheduled(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: RMQCluster| { !s.reconcile_state_contains(rabbitmq.object_ref()) })
                .leads_to(lift_state(|s: RMQCluster| {
                    &&& !s.reconcile_state_contains(rabbitmq.object_ref())
                    &&& s.reconcile_scheduled_for(rabbitmq.object_ref())
                }))
        ),
{
    let pre = |s: RMQCluster| {
        &&& !s.reconcile_state_contains(rabbitmq.object_ref())
        &&& !s.reconcile_scheduled_for(rabbitmq.object_ref())
    };
    let post = |s: RMQCluster| {
        &&& !s.reconcile_state_contains(rabbitmq.object_ref())
        &&& s.reconcile_scheduled_for(rabbitmq.object_ref())
    };
    let input = rabbitmq.object_ref();

    RMQCluster::lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec(
        spec, input, RMQCluster::next(), RMQCluster::desired_state_is(rabbitmq), pre, post
    );
    valid_implies_implies_leads_to(spec, lift_state(post), lift_state(post));
    or_leads_to_combine(spec, pre, post, post);
    temp_pred_equality(lift_state(pre).or(lift_state(post)), lift_state(|s: RMQCluster| {!s.reconcile_state_contains(rabbitmq.object_ref())}));
}

proof fn lemma_from_scheduled_to_init_step(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_scheduled_key_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(RMQCluster::the_object_in_schedule_has_spec_and_uid_as(rabbitmq)))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: RMQCluster| {
                &&& !s.reconcile_state_contains(rabbitmq.object_ref())
                &&& s.reconcile_scheduled_for(rabbitmq.object_ref())
            })
                .leads_to(lift_state(no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init)))
        ),
{
    let pre = |s: RMQCluster| {
        &&& !s.reconcile_state_contains(rabbitmq.object_ref())
        &&& s.reconcile_scheduled_for(rabbitmq.object_ref())
    };
    let post = no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init);
    let input = (None, None, Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::each_scheduled_key_is_consistent_with_its_object()(s)
        &&& RMQCluster::the_object_in_schedule_has_spec_and_uid_as(rabbitmq)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::each_scheduled_key_is_consistent_with_its_object()),
        lift_state(RMQCluster::the_object_in_schedule_has_spec_and_uid_as(rabbitmq))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
        .and(lift_state(RMQCluster::each_scheduled_key_is_consistent_with_its_object()))
        .and(lift_state(RMQCluster::the_object_in_schedule_has_spec_and_uid_as(rabbitmq)))
    );

    RMQCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next,
        RMQCluster::run_scheduled_reconcile(), pre, post
    );
}

proof fn lemma_from_init_step_to_after_create_headless_service_step(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init))
                .leads_to(lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateHeadlessService, rabbitmq)))
        ),
{
    let pre = no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init);
    let post = pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateHeadlessService, rabbitmq);
    let input = (None, None, Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(input) => {
                if input.2.get_Some_0() != rabbitmq.object_ref() {
                    assert(pre(s_prime));
                } else {
                    assert(post(s_prime));
                }
            },
            _ => {
                assert(pre(s_prime));
            }
        }
    }

    RMQCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, RMQCluster::continue_reconcile(), pre, post);
}

// This lemma ensures that rabbitmq controller at some step with pending request in flight will finally enter its next step.
// For step and next_step, they both require the reconcile_state to have a pending request which is the correct request for that step.
// Note that in this lemma we add some constraints to step:
//    1. There is only one possible next_step for it.
//    2. When the controller enters the next step, it must create a request that satisfies some requirements (which is piggybacked
// by the pending request message)
proof fn lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, step: RabbitmqReconcileStep, next_step: RabbitmqReconcileStep
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        step != RabbitmqReconcileStep::Error, step != RabbitmqReconcileStep::Done,
        // We have to use a quantifier here because we have no idea of what the cr is when conducting reconcile_core.
        // We don't have the triggering cr is the same as the rabbitmq here by `at_rabbitmq_step_with_rabbitmq`. Fortunately,
        // having the same reference, spec and uid (which is required by `at_rabbitmq_step_with_rabbitmq`) is enough for
        // proving that the returned request is valid.
        forall |any_rabbitmq, resp_o|
            #[trigger] reconcile_core(any_rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).0.reconcile_step == next_step
            && reconcile_core(any_rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).1.is_Some()
            && reconcile_core(any_rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).1.get_Some_0().is_KRequest()
            && (
                any_rabbitmq.object_ref() == rabbitmq.object_ref() && any_rabbitmq.spec() == rabbitmq.spec() && any_rabbitmq.metadata().uid == rabbitmq.metadata().uid
                ==> is_correct_pending_request_at_rabbitmq_step(next_step, reconcile_core(any_rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).1.get_Some_0().get_KRequest_0(), rabbitmq)
            ),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(step, rabbitmq))
            .leads_to(lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(next_step, rabbitmq)))
        ),
{
    // The proof of this lemma contains of two parts (two leads_to's) and then a leads_to_trans:
    //     1. at_step(step) /\ pending_request in flight /\ correct_request ~>
    //                         at_step(step) /\ response in flight /\ match(response, pending_request)
    //     2. at_step(step) /\ response in flight /\ match(response, pending_request) ~>
    //                         at_step(next_step) /\ pending_request in flight /\ correct_request
    // This predicate is used to give a specific request for the pre state for using wf1 which requires an input.
    let pre_and_req_in_flight = |req_msg| lift_state(
        req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, req_msg)
    );
    // This predicate is the intermediate state of the two leads_to
    let pre_and_exists_resp_in_flight = lift_state(
        exists_resp_in_flight_at_rabbitmq_step_with_rabbitmq(step, rabbitmq)
    );
    // This predicate is used to give a specific request for the intermediate state for using wf1 which requires an input.
    let pre_and_resp_in_flight = |resp_msg| lift_state(
        resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, resp_msg)
    );
    // We use the lemma lemma_receives_some_resp_at_rabbitmq_step_with_rabbitmq that takes a req_msg,
    // so we need to eliminate the req_msg using leads_to_exists_intro.
    assert forall |req_msg|
        spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight))
    by {
        lemma_receives_some_resp_at_rabbitmq_step_with_rabbitmq(spec, rabbitmq, req_msg, step);
    }
    leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
    assert_by(
        tla_exists(pre_and_req_in_flight) == lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(step, rabbitmq)),
        {
            assert forall |ex|
                #[trigger] lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(step, rabbitmq)).satisfied_by(ex)
            implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().pending_req_of(rabbitmq.object_ref());
                assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(
                tla_exists(pre_and_req_in_flight),
                lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(step, rabbitmq))
            );
        }
    );
    // Similarly we eliminate resp_msg using leads_to_exists_intro.
    assert forall |resp_msg|
        spec.entails(
            #[trigger] pre_and_resp_in_flight(resp_msg)
                .leads_to(lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(next_step, rabbitmq)))
        )
    by {
        lemma_from_resp_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, rabbitmq, resp_msg, step, next_step);
    }
    leads_to_exists_intro(
        spec,
        pre_and_resp_in_flight,
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(next_step, rabbitmq))
    );
    assert_by(
        tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight,
        {
            assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex)
            implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().message_in_flight(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, ex.head().pending_req_of(rabbitmq.object_ref()))
                };
                assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
        }
    );

    leads_to_trans_temp(
        spec,
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(step, rabbitmq)),
        pre_and_exists_resp_in_flight,
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(next_step, rabbitmq))
    );
}

proof fn lemma_receives_some_resp_at_rabbitmq_step_with_rabbitmq(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, req_msg: Message, step: RabbitmqReconcileStep
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        step != RabbitmqReconcileStep::Error, step != RabbitmqReconcileStep::Done,
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, req_msg))
                .leads_to(lift_state(exists_resp_in_flight_at_rabbitmq_step_with_rabbitmq(step, rabbitmq)))
        ),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, req_msg);
    let post = exists_resp_in_flight_at_rabbitmq_step_with_rabbitmq(step, rabbitmq);
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
        .and(lift_state(RMQCluster::busy_disabled()))
        .and(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && RMQCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = RMQCluster::transition_by_etcd(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        });
    }

    RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(spec, input, stronger_next, RMQCluster::handle_request(), pre, post);
}

// This lemma ensures that rabbitmq controller at some step with a response in flight that matches its pending request will finally enter its next step.
// For step and next_step, they both require the reconcile_state to have a pending request which is the correct request
// for that step. For step alone, there is a known response (the parameter resp_msg) in flight that matches the pending request.
// Note that in this lemma we add some constraints to step:
//    1. There is only one possible next_step for it.
//    2. When the controller enters this step, it must creates a request (which will be used to create the pending request message)
proof fn lemma_from_resp_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, resp_msg: Message, step: RabbitmqReconcileStep, result_step: RabbitmqReconcileStep
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        step != RabbitmqReconcileStep::Done, step != RabbitmqReconcileStep::Error,
        // We have to use a quantifier here because we have no idea of what the cr is when conducting reconcile_core.
        // We don't have the triggering cr is the same as the rabbitmq here by `at_rabbitmq_step_with_rabbitmq`. Fortunately,
        // having the same reference, spec and uid (which is required by `at_rabbitmq_step_with_rabbitmq`) is enough for
        // proving that the returned request is valid.
        forall |any_rabbitmq, resp_o|
            #[trigger] reconcile_core(any_rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).0.reconcile_step == result_step
            && reconcile_core(any_rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).1.is_Some()
            && reconcile_core(any_rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).1.get_Some_0().is_KRequest()
            && (
                any_rabbitmq.object_ref() == rabbitmq.object_ref() && any_rabbitmq.spec() == rabbitmq.spec() && any_rabbitmq.metadata().uid == rabbitmq.metadata().uid
                ==> is_correct_pending_request_at_rabbitmq_step(result_step, reconcile_core(any_rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).1.get_Some_0().get_KRequest_0(), rabbitmq)
            ),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, resp_msg))
                .leads_to(lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(result_step, rabbitmq)))
        ),
{
    let pre = resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, resp_msg);
    let post = pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(result_step, rabbitmq);
    let input = (Some(resp_msg), None, Some(rabbitmq.object_ref()));

    // For every part of stronger_next:
    //   - next(): the next predicate of the state machine
    //   - RMQCluster::crash_disabled(): to ensure that the reconcile process can continue
    //   - RMQCluster::busy_disabled(): to ensure that the request will get its expected response
    //    (Note that this is not required for termination)
    //   - each_resp_matches_at_most_one_pending_req: to make sure that the resp_msg will not be used by other cr
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())(s)
    };

    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
        .and(lift_state(RMQCluster::busy_disabled()))
        .and(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(input) => {
                if input.2.is_Some() && input.2.get_Some_0() == rabbitmq.object_ref() {
                    assert(s_prime.reconcile_state_of(rabbitmq.object_ref()).local_state.reconcile_step == result_step);
                    assert(post(s_prime));
                } else {
                    assert(pre(s_prime));
                }
            }
            _ => {
                assert(pre(s_prime));
            }
        }
    }

    RMQCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, RMQCluster::continue_reconcile(), pre, post);
}

proof fn lemma_from_after_get_server_config_map_to_rabbitmq_matches(rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
    ensures
        next_with_wf_and_assumption_and_all_invariants(rabbitmq)
        .entails(
            lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)).leads_to(lift_state(current_config_map_matches(rabbitmq)))
        ),
{
    let spec = next_with_wf_and_assumption_and_all_invariants(rabbitmq);
    lemma_from_after_get_server_config_map_and_key_not_exists_to_rabbitmq_matches(rabbitmq);
    lemma_from_after_get_server_config_map_and_key_exists_to_rabbitmq_matches(rabbitmq);
    let key_not_exists = |s: RMQCluster| {
            &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)(s)
    };
    let key_exists = |s: RMQCluster| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)(s)
    };
    or_leads_to_combine(spec, key_not_exists, key_exists, current_config_map_matches(rabbitmq));
    temp_pred_equality(
        lift_state(key_not_exists).or(lift_state(key_exists)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq))
    );
}

proof fn lemma_from_after_get_server_config_map_and_key_not_exists_to_rabbitmq_matches(rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
    ensures
        next_with_wf_and_assumption_and_all_invariants(rabbitmq)
        .entails(
            lift_state(|s: RMQCluster| {
                &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)(s)
            }).leads_to(lift_state(current_config_map_matches(rabbitmq)))
        ),
        next_with_wf_and_assumption_and_all_invariants(rabbitmq)
        .entails(
            lift_state(|s: RMQCluster| {
                &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)(s)
            }).leads_to(lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServiceAccount, rabbitmq)))
        ),
{
    let spec = next_with_wf_and_assumption_and_all_invariants(rabbitmq);
    let pre = lift_state(|s: RMQCluster| {
        &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)(s)
    });
    let post = lift_state(|s: RMQCluster| {
        &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServerConfigMap, rabbitmq)(s)
    });
    let pre_and_req_in_flight = |req_msg| lift_state(
        |s: RMQCluster| {
            &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, req_msg)(s)
        }
    );
    let pre_and_exists_resp_in_flight = lift_state(
        |s: RMQCluster| {
            &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& at_after_get_server_config_map_step_with_rabbitmq_and_exists_not_found_resp_in_flight(rabbitmq)(s)
        }
    );
    let pre_and_resp_in_flight = |resp_msg| lift_state(
        |s: RMQCluster| {
            &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, resp_msg)(s)
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    );
    let post_and_req_in_flight = |req_msg| lift_state(
        |s: RMQCluster| {
            &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServerConfigMap, rabbitmq, req_msg)(s)
        }
    );
    assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight))
    by {
        lemma_receives_not_found_resp_at_after_get_server_config_map_step_with_rabbitmq(spec, rabbitmq, req_msg);
    }
    leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
    assert_by(
        tla_exists(pre_and_req_in_flight) == pre,
        {
            assert forall |ex| #[trigger] pre.satisfied_by(ex)
            implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().pending_req_of(rabbitmq.object_ref());
                assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_req_in_flight), pre);
        }
    );

    assert forall |resp_msg| spec.entails(#[trigger] pre_and_resp_in_flight(resp_msg).leads_to(post))
    by {
        lemma_from_after_get_server_config_map_step_to_after_create_server_config_map_step(spec, rabbitmq, resp_msg);
    }
    leads_to_exists_intro(spec, pre_and_resp_in_flight, post);
    assert_by(
        tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight,
        {
            assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex)
            implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().message_in_flight(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, ex.head().pending_req_of(rabbitmq.object_ref()))
                    &&& resp_msg.content.get_get_response().res.is_Err()
                    &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
                };
                assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
        }
    );

    assert forall |req_msg| spec.entails(#[trigger] post_and_req_in_flight(req_msg).leads_to(lift_state(current_config_map_matches(rabbitmq))))
    by {
        lemma_cm_is_created_at_after_create_server_config_map_step_with_rabbitmq(spec, rabbitmq, req_msg);
    }
    leads_to_exists_intro(spec, post_and_req_in_flight, lift_state(current_config_map_matches(rabbitmq)));
    assert_by(
        tla_exists(post_and_req_in_flight) == post,
        {
            assert forall |ex| #[trigger] post.satisfied_by(ex)
            implies tla_exists(post_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().pending_req_of(rabbitmq.object_ref());
                assert(post_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(post_and_req_in_flight), post);
        }
    );

    leads_to_trans_temp(spec, pre, pre_and_exists_resp_in_flight, post);
    leads_to_trans_temp(spec, pre, post, lift_state(current_config_map_matches(rabbitmq)));

    valid_implies_implies_leads_to(spec, post, lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServerConfigMap, rabbitmq)));
    lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, rabbitmq, RabbitmqReconcileStep::AfterCreateServerConfigMap, RabbitmqReconcileStep::AfterCreateServiceAccount);
    leads_to_trans_n!(
        spec, pre, post, 
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServerConfigMap, rabbitmq)), 
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServiceAccount, rabbitmq))
    );
}

proof fn lemma_receives_not_found_resp_at_after_get_server_config_map_step_with_rabbitmq(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, req_msg: Message
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::at_most_one_create_cm_req_is_in_flight(rabbitmq.object_ref())))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: RMQCluster| {
                    &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                    &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, req_msg)(s)
                }
            )
                .leads_to(lift_state(
                    |s: RMQCluster| {
                        &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                        &&& at_after_get_server_config_map_step_with_rabbitmq_and_exists_not_found_resp_in_flight(rabbitmq)(s)
                    }
                ))
        ),
{
    let pre = |s: RMQCluster| {
        &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, req_msg)(s)
    };
    let post = |s: RMQCluster| {
        &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& at_after_get_server_config_map_step_with_rabbitmq_and_exists_not_found_resp_in_flight(rabbitmq)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::at_most_one_create_cm_req_is_in_flight(rabbitmq.object_ref())(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::at_most_one_create_cm_req_is_in_flight(rabbitmq.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
        .and(lift_state(RMQCluster::busy_disabled()))
        .and(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))
        .and(lift_state(helper_invariants::at_most_one_create_cm_req_is_in_flight(rabbitmq.object_ref())))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = RMQCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
                    assert({
                        &&& s_prime.message_in_flight(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.get_get_response().res.is_Err()
                        &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
                    });
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && RMQCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = RMQCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        });
    }

    RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, RMQCluster::handle_request(), pre, post
    );
}

proof fn lemma_from_after_get_server_config_map_step_to_after_create_server_config_map_step(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, resp_msg: Message
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::at_most_one_create_cm_req_is_in_flight(rabbitmq.object_ref())))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: RMQCluster| {
                &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                &&& resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, resp_msg)(s)
                &&& resp_msg.content.get_get_response().res.is_Err()
                &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
            })
                .leads_to(lift_state(|s: RMQCluster| {
                    &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                    &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServerConfigMap, rabbitmq)(s)
                }))
        ),
{
    let pre = |s: RMQCluster| {
        &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, resp_msg)(s)
        &&& resp_msg.content.get_get_response().res.is_Err()
        &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
    };
    let post = |s: RMQCluster| {
        &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServerConfigMap, rabbitmq)(s)
    };
    let input = (Some(resp_msg), None, Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())(s)
        &&& RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())(s)
        &&& helper_invariants::at_most_one_create_cm_req_is_in_flight(rabbitmq.object_ref())(s)
    };

    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())),
        lift_state(helper_invariants::at_most_one_create_cm_req_is_in_flight(rabbitmq.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
        .and(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))
        .and(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))
        .and(lift_state(helper_invariants::at_most_one_create_cm_req_is_in_flight(rabbitmq.object_ref())))
    );

    RMQCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next,
        RMQCluster::continue_reconcile(), pre, post
    );
}

proof fn lemma_cm_is_created_at_after_create_server_config_map_step_with_rabbitmq(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, req_msg: Message
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::at_most_one_create_cm_req_is_in_flight(rabbitmq.object_ref())))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: RMQCluster| {
                    &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                    &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServerConfigMap, rabbitmq, req_msg)(s)
                }
            )
                .leads_to(lift_state(
                    |s: RMQCluster| {
                        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).is_Ok()
                        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).get_Ok_0().data == make_server_config_map(rabbitmq).data
                    }
                ))
        ),
{
    let pre = |s: RMQCluster| {
        &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServerConfigMap, rabbitmq, req_msg)(s)
    };
    let post = |s: RMQCluster| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).is_Ok()
        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).get_Ok_0().data == make_server_config_map(rabbitmq).data
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::at_most_one_create_cm_req_is_in_flight(rabbitmq.object_ref())(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::at_most_one_create_cm_req_is_in_flight(rabbitmq.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
        .and(lift_state(RMQCluster::busy_disabled()))
        .and(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))
        .and(lift_state(helper_invariants::at_most_one_create_cm_req_is_in_flight(rabbitmq.object_ref())))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                ConfigMapView::spec_integrity_is_preserved_by_marshal();
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && RMQCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        ConfigMapView::spec_integrity_is_preserved_by_marshal();
    }

    RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, RMQCluster::handle_request(), pre, post
    );
}

proof fn lemma_from_after_get_server_config_map_and_key_exists_to_rabbitmq_matches(rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
    ensures
        next_with_wf_and_assumption_and_all_invariants(rabbitmq)
        .entails(
            lift_state(|s: RMQCluster| {
                &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)(s)
            }).leads_to(lift_state(current_config_map_matches(rabbitmq)))
        ),
        next_with_wf_and_assumption_and_all_invariants(rabbitmq)
        .entails(
            lift_state(|s: RMQCluster| {
                &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)(s)
            }).leads_to(lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServiceAccount, rabbitmq)))
        ),
{
    let spec = next_with_wf_and_assumption_and_all_invariants(rabbitmq);
    let pre = lift_state(|s: RMQCluster| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)(s)
    });
    let pre_with_object = |object| lift_state(
        |s: RMQCluster| {
            &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
            &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)(s)
        }
    );
    let post_with_object = |object| lift_state(
        |s: RMQCluster| {
            &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
            &&& pending_req_with_object_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, object)(s)
        }
    );
    assert forall |object: DynamicObjectView| spec.entails(#[trigger] pre_with_object(object).leads_to(post_with_object(object))) by
    {
        let p1 = lift_state(|s: RMQCluster| {
            &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
            &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)(s)
        });
        let p2 = lift_state(|s: RMQCluster| {
            &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
            &&& pending_req_with_object_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, object)(s)
        });

        assert_by(
            spec.entails(p1.leads_to(p2)),
            {
                let pre_and_req_in_flight = |req_msg| lift_state(
                    |s: RMQCluster| {
                        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                        &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, req_msg)(s)
                    }
                );
                let pre_and_exists_resp_in_flight = lift_state(
                    |s: RMQCluster| {
                        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                        &&& at_after_get_server_config_map_step_with_rabbitmq_and_exists_ok_resp_in_flight(rabbitmq, object)(s)
                    }
                );
                let pre_and_resp_in_flight = |resp_msg| lift_state(
                    |s: RMQCluster| {
                        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                        &&& resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, resp_msg)(s)
                        &&& resp_msg.content.get_get_response().res.is_Ok()
                        &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
                    }
                );

                assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight))
                by {
                    lemma_receives_ok_resp_at_after_get_server_config_map_step_with_rabbitmq(spec, rabbitmq, req_msg, object);
                }
                leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
                assert_by(
                    tla_exists(pre_and_req_in_flight) == p1,
                    {
                        assert forall |ex| #[trigger] p1.satisfied_by(ex)
                        implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                            let req_msg = ex.head().pending_req_of(rabbitmq.object_ref());
                            assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
                        }
                        temp_pred_equality(tla_exists(pre_and_req_in_flight), p1);
                    }
                );

                assert forall |resp_msg| spec.entails(#[trigger] pre_and_resp_in_flight(resp_msg).leads_to(p2))
                by {
                    lemma_from_after_get_server_config_map_step_to_after_update_server_config_map_step(spec, rabbitmq, resp_msg, object);
                }
                leads_to_exists_intro(spec, pre_and_resp_in_flight, p2);
                assert_by(
                    tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight,
                    {
                        assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex)
                        implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                            let resp_msg = choose |resp_msg| {
                                &&& #[trigger] ex.head().message_in_flight(resp_msg)
                                &&& resp_msg_matches_req_msg(resp_msg, ex.head().pending_req_of(rabbitmq.object_ref()))
                                &&& resp_msg.content.get_get_response().res.is_Ok()
                                &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
                            };
                            assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
                        }
                        temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
                    }
                );

                leads_to_trans_temp(spec, p1, pre_and_exists_resp_in_flight, p2);
            }
        );
    }
    assert forall |object: DynamicObjectView| spec.entails(#[trigger] pre_with_object(object).leads_to(lift_state(current_config_map_matches(rabbitmq)))) by {   
        assert(spec.entails(pre_with_object(object).leads_to(post_with_object(object))));
        assert_by(
            spec.entails(post_with_object(object).leads_to(lift_state(current_config_map_matches(rabbitmq)))),
            {
                let pre_and_req_in_flight = |req_msg| lift_state(
                    |s: RMQCluster| {
                        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                        &&& req_msg_is_the_in_flight_pending_req_with_object_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, req_msg, object)(s)
                    }
                );
                assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(lift_state(current_config_map_matches(rabbitmq))))
                by {
                    lemma_cm_is_updated_at_after_update_server_config_map_step_with_rabbitmq(spec, rabbitmq, req_msg, object);
                }
                leads_to_exists_intro(spec, pre_and_req_in_flight, lift_state(current_config_map_matches(rabbitmq)));
                assert_by(
                    tla_exists(pre_and_req_in_flight) == post_with_object(object),
                    {
                        assert forall |ex| #[trigger] post_with_object(object).satisfied_by(ex)
                        implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                            let req_msg = ex.head().pending_req_of(rabbitmq.object_ref());
                            assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
                        }
                        temp_pred_equality(tla_exists(pre_and_req_in_flight), post_with_object(object));
                    }
                );
            }
        );
        leads_to_trans_temp(spec, pre_with_object(object), post_with_object(object), lift_state(current_config_map_matches(rabbitmq)));
    }
    assert forall |object: DynamicObjectView| spec.entails(#[trigger] pre_with_object(object).leads_to(lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServiceAccount, rabbitmq)))) by {
        valid_implies_implies_leads_to(spec, post_with_object(object), lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq)));
        lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, rabbitmq, RabbitmqReconcileStep::AfterUpdateServerConfigMap, RabbitmqReconcileStep::AfterCreateServiceAccount);
        leads_to_trans_n!(
            spec, pre_with_object(object), post_with_object(object), 
            lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq)), 
            lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServiceAccount, rabbitmq))
        );
    }
    leads_to_exists_intro(spec, pre_with_object, lift_state(current_config_map_matches(rabbitmq)));
    leads_to_exists_intro(spec, pre_with_object, lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServiceAccount, rabbitmq)));
    assert_by(
        tla_exists(pre_with_object) == pre,
        {
            assert forall |ex| #[trigger] pre.satisfied_by(ex)
            implies tla_exists(pre_with_object).satisfied_by(ex) by {
                let object = ex.head().resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()));
                assert(pre_with_object(object).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_with_object), pre);
        }
    );
}

proof fn lemma_receives_ok_resp_at_after_get_server_config_map_step_with_rabbitmq(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, req_msg: Message, object: DynamicObjectView
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::at_most_one_update_cm_req_is_in_flight(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref())))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: RMQCluster| {
                    &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                    &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                    &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, req_msg)(s)
                }
            )
                .leads_to(lift_state(
                    |s: RMQCluster| {
                        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                        &&& at_after_get_server_config_map_step_with_rabbitmq_and_exists_ok_resp_in_flight(rabbitmq, object)(s)
                    }
                ))
        ),
{
    let pre = |s: RMQCluster| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
        &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, req_msg)(s)
    };
    let post = |s: RMQCluster| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
        &&& at_after_get_server_config_map_step_with_rabbitmq_and_exists_ok_resp_in_flight(rabbitmq, object)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::at_most_one_update_cm_req_is_in_flight(rabbitmq.object_ref())(s)
        &&& helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref())(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::at_most_one_update_cm_req_is_in_flight(rabbitmq.object_ref())),
        lift_state(helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
        .and(lift_state(RMQCluster::busy_disabled()))
        .and(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))
        .and(lift_state(helper_invariants::at_most_one_update_cm_req_is_in_flight(rabbitmq.object_ref())))
        .and(lift_state(helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref())))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = RMQCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
                    assert({
                        &&& s_prime.message_in_flight(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.get_get_response().res.is_Ok()
                        &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
                    });
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && RMQCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = RMQCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
        });
    }

    RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, RMQCluster::handle_request(), pre, post
    );
}

// Skip this lemma for now; we will need an invariant saying that the configmap object never has a deletion timestamp.
// Note that this variant only holds since the CR always exists and the old configmap owned by the old CR has been deleted.
#[verifier(external_body)]
proof fn lemma_cm_is_updated_at_after_update_server_config_map_step_with_rabbitmq(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, req_msg: Message, object: DynamicObjectView
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::at_most_one_update_cm_req_is_in_flight(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref())))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: RMQCluster| {
                    &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                    &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                    &&& req_msg_is_the_in_flight_pending_req_with_object_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, req_msg, object)(s)
                }
            )
                .leads_to(lift_state(
                    |s: RMQCluster| {
                        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).is_Ok()
                        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).get_Ok_0().data == make_server_config_map(rabbitmq).data
                    }
                ))
        ),
{
    let pre = |s: RMQCluster| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
        &&& req_msg_is_the_in_flight_pending_req_with_object_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, req_msg, object)(s)
    };
    let post = |s: RMQCluster| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).is_Ok()
        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).get_Ok_0().data == make_server_config_map(rabbitmq).data
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& helper_invariants::at_most_one_update_cm_req_is_in_flight(rabbitmq.object_ref())(s)
        &&& helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref())(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(helper_invariants::at_most_one_update_cm_req_is_in_flight(rabbitmq.object_ref())),
        lift_state(helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
        .and(lift_state(RMQCluster::busy_disabled()))
        .and(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))
        .and(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))
        .and(lift_state(helper_invariants::at_most_one_update_cm_req_is_in_flight(rabbitmq.object_ref())))
        .and(lift_state(helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref())))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                ConfigMapView::spec_integrity_is_preserved_by_marshal();
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && RMQCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        ConfigMapView::spec_integrity_is_preserved_by_marshal();
    }

    RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, RMQCluster::handle_request(), pre, post
    );
}

proof fn lemma_from_after_get_server_config_map_step_to_after_update_server_config_map_step(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, resp_msg: Message, object: DynamicObjectView
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::at_most_one_update_cm_req_is_in_flight(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref())))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: RMQCluster| {
                &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                &&& resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, resp_msg)(s)
                &&& resp_msg.content.get_get_response().res.is_Ok()
                &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
            })
                .leads_to(lift_state(|s: RMQCluster| {
                    &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                    &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                    &&& pending_req_with_object_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, object)(s)
                }))
        ),
{
    let pre = |s: RMQCluster| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
        &&& resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, resp_msg)(s)
        &&& resp_msg.content.get_get_response().res.is_Ok()
        &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
    };
    let post = |s: RMQCluster| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
        &&& pending_req_with_object_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, object)(s)
    };
    let input = (Some(resp_msg), None, Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())(s)
        &&& RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& helper_invariants::at_most_one_update_cm_req_is_in_flight(rabbitmq.object_ref())(s)
        &&& helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref())(s)
    };

    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(helper_invariants::at_most_one_update_cm_req_is_in_flight(rabbitmq.object_ref())),
        lift_state(helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
        .and(lift_state(RMQCluster::busy_disabled()))
        .and(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))
        .and(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))
        .and(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))
        .and(lift_state(helper_invariants::at_most_one_update_cm_req_is_in_flight(rabbitmq.object_ref())))
        .and(lift_state(helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref())))
    );

    RMQCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next,
        RMQCluster::continue_reconcile(), pre, post
    );
}

pub open spec fn sts_key_not_exists_or_delete_msg_in_flight_or_sts_has_current_ref(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    let sts_key = make_stateful_set_key(rabbitmq.object_ref());
    |s: RMQCluster| {
        ||| {
            &&& s.resource_key_exists(sts_key)
            &&& (
                    (exists |msg: Message| {
                        #[trigger] s.message_in_flight(msg)
                        && msg.dst.is_KubernetesAPI()
                        && msg.content.is_delete_request_with_key(sts_key)
                    })
                    || s.resource_obj_of(sts_key).metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
            )
        }
        ||| !s.resource_key_exists(sts_key)
    }
}

proof fn lemma_eventually_only_valid_stateful_set_exists(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_only_has_controller_owner_ref(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_update_sts_req_does_the_same(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_create_sts_req_does_the_same(rabbitmq)))),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(helper_invariants::stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq))))),
{
    let sts_key = make_stateful_set_key(rabbitmq.object_ref());
    let key_not_exists = |s: RMQCluster| !s.resource_key_exists(sts_key);
    let key_exists_and_current_ref = |s: RMQCluster| {
        s.resource_key_exists(sts_key)
        && s.resource_obj_of(make_stateful_set_key(rabbitmq.object_ref())).metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    };
    let key_exists_and_old_ref = |s: RMQCluster| {
        s.resource_key_exists(sts_key)
        && exists |uid: nat| #![auto]
        uid != rabbitmq.metadata.uid.get_Some_0() && s.resource_obj_of(make_stateful_set_key(rabbitmq.object_ref())).metadata.owner_references == Some(seq![OwnerReferenceView {
            block_owner_deletion: None,
            controller: Some(true),
            kind: RabbitmqClusterView::kind(),
            name: rabbitmq.metadata.name.get_Some_0(),
            uid: uid,
        }])
    };
    let delete_msg_in_flight = sts_key_not_exists_or_delete_msg_in_flight_or_sts_has_current_ref(rabbitmq);
    implies_to_leads_to(spec, lift_state(key_not_exists), lift_state(delete_msg_in_flight));
    implies_to_leads_to(spec, lift_state(key_exists_and_current_ref), lift_state(delete_msg_in_flight));
    let post = helper_invariants::stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq);
    let input = (BuiltinControllerChoice::GarbageCollector, sts_key);
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::desired_state_is(rabbitmq)(s)
        &&& helper_invariants::stateful_set_only_has_controller_owner_ref(rabbitmq)(s)
        &&& helper_invariants::every_update_sts_req_does_the_same(rabbitmq)(s)
        &&& helper_invariants::every_create_sts_req_does_the_same(rabbitmq)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::desired_state_is(rabbitmq)),
        lift_state(helper_invariants::stateful_set_only_has_controller_owner_ref(rabbitmq)),
        lift_state(helper_invariants::every_update_sts_req_does_the_same(rabbitmq)),
        lift_state(helper_invariants::every_create_sts_req_does_the_same(rabbitmq))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::desired_state_is(rabbitmq)))
        .and(lift_state(helper_invariants::stateful_set_only_has_controller_owner_ref(rabbitmq)))
        .and(lift_state(helper_invariants::every_update_sts_req_does_the_same(rabbitmq)))
        .and(lift_state(helper_invariants::every_create_sts_req_does_the_same(rabbitmq)))
    );

    assert forall |s, s_prime: RMQCluster| key_exists_and_old_ref(s) && #[trigger] stronger_next(s, s_prime) && RMQCluster::builtin_controllers_next().forward(input)(s, s_prime) implies delete_msg_in_flight(s_prime) by {
        let owner_references = s.resource_obj_of(make_stateful_set_key(rabbitmq.object_ref())).metadata.owner_references.get_Some_0();
        assert(owner_references.len() == 1);
        let new_delete_msg = built_in_controller_req_msg(delete_req_msg_content(
            sts_key, s.rest_id_allocator.allocate().1
        ));
        assert(s_prime.resource_key_exists(sts_key));
        assert(s_prime.message_in_flight(new_delete_msg));
    }

    assert forall |s, s_prime: RMQCluster| key_exists_and_old_ref(s) && #[trigger] stronger_next(s, s_prime) implies key_exists_and_old_ref(s_prime) || delete_msg_in_flight(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::BuiltinControllersStep(i) => {
                if i == input {
                    assert(delete_msg_in_flight(s_prime));
                } else {
                    assert(key_exists_and_old_ref(s_prime));
                }
            },
            Step::KubernetesAPIStep(i) => {
                if i.get_Some_0().content.is_update_request_with_key(sts_key) {
                    if RMQCluster::validate_update_request(i.get_Some_0().content.get_update_request(), s.kubernetes_api_state).is_Some()
                    || RMQCluster::update_is_noop(i.get_Some_0().content.get_update_request().obj, s.resource_obj_of(sts_key)) {
                        assert(key_exists_and_old_ref(s_prime));
                    } else {
                        assert(i.get_Some_0().content.get_update_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()]));
                        StatefulSetView::spec_integrity_is_preserved_by_marshal();
                        assert(!s_prime.resource_key_exists(sts_key) || (s_prime.resource_key_exists(sts_key) && s_prime.resource_obj_of(sts_key).metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])));
                    }
                } else if i.get_Some_0().content.is_delete_request_with_key(sts_key) {
                    assert(s.resource_obj_of(sts_key).metadata.finalizers.is_None());
                    assert(!s_prime.resource_key_exists(sts_key));
                } else {
                    assert(key_exists_and_old_ref(s_prime));
                }
            },
            _ => {
                assert(key_exists_and_old_ref(s_prime) || delete_msg_in_flight(s_prime));
            }
        }
    }

    RMQCluster::lemma_pre_leads_to_post_by_builtin_controllers(
        spec, input, stronger_next, RMQCluster::run_garbage_collector(), key_exists_and_old_ref, delete_msg_in_flight
    );
    or_leads_to_combine_n!(
        spec,
        lift_state(key_not_exists), lift_state(key_exists_and_current_ref), lift_state(key_exists_and_old_ref);
        lift_state(delete_msg_in_flight)
    );
    implies_preserved_by_always_temp(
        lift_state(helper_invariants::stateful_set_only_has_controller_owner_ref(rabbitmq)),
        true_pred().implies(lift_state(key_not_exists).or(lift_state(key_exists_and_current_ref)).or(lift_state(key_exists_and_old_ref)))
    );
    entails_trans(
        spec,
        always(lift_state(helper_invariants::stateful_set_only_has_controller_owner_ref(rabbitmq))),
        always(true_pred().implies(lift_state(key_not_exists).or(lift_state(key_exists_and_current_ref)).or(lift_state(key_exists_and_old_ref))))
    );
    implies_to_leads_to(spec, true_pred(), lift_state(key_not_exists).or(lift_state(key_exists_and_current_ref)).or(lift_state(key_exists_and_old_ref)));
    lemma_delete_msg_in_flight_leads_to_only_valid_sts_exists(spec, rabbitmq);
    leads_to_trans_n!(
        spec,
        true_pred(), lift_state(key_not_exists).or(lift_state(key_exists_and_current_ref)).or(lift_state(key_exists_and_old_ref)),
        lift_state(delete_msg_in_flight),
        lift_state(post)
    );
    leads_to_stable(spec, stronger_next, |s: RMQCluster| true, post);
}

proof fn lemma_delete_msg_in_flight_leads_to_only_valid_sts_exists(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView
)
    requires
        rabbitmq.well_formed(),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_only_has_controller_owner_ref(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_update_sts_req_does_the_same(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_create_sts_req_does_the_same(rabbitmq)))),
    ensures
        spec.entails(lift_state(sts_key_not_exists_or_delete_msg_in_flight_or_sts_has_current_ref(rabbitmq)).leads_to(lift_state(helper_invariants::stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq)))),
{
    let pre = sts_key_not_exists_or_delete_msg_in_flight_or_sts_has_current_ref(rabbitmq);
    let post = helper_invariants::stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq);
    let sts_key = make_stateful_set_key(rabbitmq.object_ref());
    let key_exists_and_delete_msg_exists = |s: RMQCluster| {
        &&& s.resource_key_exists(sts_key)
        &&& exists |msg: Message| {
            #[trigger] s.message_in_flight(msg)
            && msg.dst.is_KubernetesAPI()
            && msg.content.is_delete_request_with_key(sts_key)
        }
    };
    let key_exists_and_current_ref = |s: RMQCluster| {
        &&& s.resource_key_exists(sts_key)
        &&& s.resource_obj_of(sts_key).metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    };
    let key_not_exists = |s: RMQCluster| !s.resource_key_exists(sts_key);
    valid_implies_implies_leads_to(spec, lift_state(key_exists_and_current_ref), lift_state(post));
    valid_implies_implies_leads_to(spec, lift_state(key_not_exists), lift_state(post));
    
    assert_by(
        spec.entails(lift_state(key_exists_and_delete_msg_exists).leads_to(lift_state(post))),
        {
            let msg_to_p = |msg: Message| {
                lift_state(|s: RMQCluster| {
                    &&& s.resource_key_exists(sts_key)
                    &&& s.message_in_flight(msg)
                    &&& msg.dst.is_KubernetesAPI()
                    &&& msg.content.is_delete_request_with_key(sts_key)
                })
            };
            assert forall |msg: Message| spec.entails((#[trigger] msg_to_p(msg)).leads_to(lift_state(post))) by {
                let input = Some(msg);
                let msg_to_p_state = |s: RMQCluster| {
                    &&& s.resource_key_exists(sts_key)
                    &&& s.message_in_flight(msg)
                    &&& msg.dst.is_KubernetesAPI()
                    &&& msg.content.is_delete_request_with_key(sts_key)
                };
                let stronger_next = |s, s_prime: RMQCluster| {
                    &&& RMQCluster::next()(s, s_prime)
                    &&& RMQCluster::busy_disabled()(s)
                    &&& helper_invariants::stateful_set_only_has_controller_owner_ref(rabbitmq)(s)
                    &&& helper_invariants::every_update_sts_req_does_the_same(rabbitmq)(s)
                };
                entails_always_and_n!(
                    spec,
                    lift_action(RMQCluster::next()),
                    lift_state(RMQCluster::busy_disabled()),
                    lift_state(helper_invariants::stateful_set_only_has_controller_owner_ref(rabbitmq)),
                    lift_state(helper_invariants::every_update_sts_req_does_the_same(rabbitmq))
                );
                temp_pred_equality(
                    lift_action(stronger_next),
                    lift_action(RMQCluster::next())
                    .and(lift_state(RMQCluster::busy_disabled()))
                    .and(lift_state(helper_invariants::stateful_set_only_has_controller_owner_ref(rabbitmq)))
                    .and(lift_state(helper_invariants::every_update_sts_req_does_the_same(rabbitmq)))
                );
                RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(spec, input, stronger_next, RMQCluster::handle_request(), msg_to_p_state, post);
            }
            leads_to_exists_intro(spec, msg_to_p, lift_state(post));
            assert_by(
                tla_exists(msg_to_p) == lift_state(key_exists_and_delete_msg_exists),
                {
                    assert forall |ex| #[trigger] lift_state(key_exists_and_delete_msg_exists).satisfied_by(ex) implies tla_exists(msg_to_p).satisfied_by(ex) by {
                        assert(ex.head().resource_key_exists(sts_key));
                        let msg = choose |msg| {
                            &&& #[trigger] ex.head().message_in_flight(msg)
                            &&& msg.dst.is_KubernetesAPI()
                            &&& msg.content.is_delete_request_with_key(sts_key)
                        };
                        assert(msg_to_p(msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(msg_to_p), lift_state(key_exists_and_delete_msg_exists));
                }
            )
        }
    );
    temp_pred_equality(
        lift_state(key_exists_and_delete_msg_exists).or(lift_state(key_exists_and_current_ref)).or(lift_state(key_not_exists)),
        lift_state(pre)
    );
    or_leads_to_combine_n!(
        spec,
        lift_state(key_exists_and_delete_msg_exists), lift_state(key_exists_and_current_ref), lift_state(key_not_exists);
        lift_state(post)
    );
}

// Skip this lemma for now; we will need an invariant saying that the configmap object never has a deletion timestamp.
// Note that this variant only holds since the CR always exists and the old configmap owned by the old CR has been deleted.
#[verifier(external_body)]
proof fn lemma_server_config_map_is_stable(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, p: TempPred<RMQCluster>
)
    requires
        spec.entails(p.leads_to(lift_state(current_config_map_matches(rabbitmq)))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_update_cm_req_does_the_same(rabbitmq)))),
    ensures
        spec.entails(p.leads_to(always(lift_state(current_config_map_matches(rabbitmq))))),
{
    let post = current_config_map_matches(rabbitmq);
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref())(s)
        &&& helper_invariants::every_update_cm_req_does_the_same(rabbitmq)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref())),
        lift_state(helper_invariants::every_update_cm_req_does_the_same(rabbitmq))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(helper_invariants::no_delete_cm_req_is_in_flight(rabbitmq.object_ref())))
        .and(lift_state(helper_invariants::every_update_cm_req_does_the_same(rabbitmq)))
    );

    assert forall |s, s_prime| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        ConfigMapView::spec_integrity_is_preserved_by_marshal();
    }

    leads_to_stable_temp(spec, lift_action(stronger_next), p, lift_state(post));
}

}
