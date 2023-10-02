// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    common::*,
    proof::{common::*, helper_invariants},
    spec::{reconciler::*, types::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// We prove init /\ []next /\ []wf |= []RMQCluster::desired_state_is(rabbitmq) ~> []current_state_matches(rabbitmq) holds for each rabbitmq.
proof fn liveness_proof_forall_rabbitmq()
    ensures
        forall |rabbitmq: RabbitmqClusterView| rabbitmq.well_formed() ==> #[trigger] cluster_spec().entails(liveness(rabbitmq)),
{
    assert forall |rabbitmq: RabbitmqClusterView| rabbitmq.well_formed()
    implies #[trigger] cluster_spec().entails(liveness(rabbitmq)) by {
        liveness_proof(rabbitmq);
    };
}

proof fn liveness_proof(rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
    ensures
        cluster_spec().entails(liveness(rabbitmq)),
{
    lemma_true_leads_to_always_current_state_matches_rabbitmq_under_eventual_invariants(rabbitmq);

    always_p_is_stable(lift_state(RMQCluster::desired_state_is(rabbitmq)));
    invariants_is_stable(rabbitmq);
    invariants_since_phase_I_is_stable(rabbitmq);
    invariants_since_phase_II_is_stable(rabbitmq);
    invariants_since_phase_III_is_stable(rabbitmq);
    invariants_since_phase_IV_is_stable(rabbitmq);
    stable_and_n!(
        invariants(rabbitmq),
        always(lift_state(RMQCluster::desired_state_is(rabbitmq))),
        invariants_since_phase_I(rabbitmq),
        invariants_since_phase_II(rabbitmq),
        invariants_since_phase_III(rabbitmq),
        invariants_since_phase_IV(rabbitmq)
    );
    // Eliminate all the invariants by phase.
    assert_by(
        invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(invariants_since_phase_I(rabbitmq)).and(invariants_since_phase_II(rabbitmq)).and(invariants_since_phase_III(rabbitmq)).and(invariants_since_phase_IV(rabbitmq))
        .entails(
            true_pred().leads_to(always(current_state_matches(rabbitmq)))
        ),
        {
            let spec = invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(invariants_since_phase_I(rabbitmq)).and(invariants_since_phase_II(rabbitmq)).and(invariants_since_phase_III(rabbitmq)).and(invariants_since_phase_IV(rabbitmq));
            unpack_conditions_from_spec(spec, invariants_since_phase_V(rabbitmq), true_pred(), always(current_state_matches(rabbitmq)));
            temp_pred_equality(true_pred().and(invariants_since_phase_V(rabbitmq)), invariants_since_phase_V(rabbitmq));
            eliminate_always(spec, lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()));
            helper_invariants::lemma_true_leads_to_always_no_delete_sts_req_is_in_flight(spec, rabbitmq);
            helper_invariants::lemma_true_leads_to_always_no_delete_cm_req_is_in_flight(spec, rabbitmq);
            leads_to_always_combine_temp(
                spec, true_pred(),
                lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(make_stateful_set_key(rabbitmq.object_ref()))),
                lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(make_server_config_map_key(rabbitmq.object_ref())))
            );
            leads_to_trans_temp(spec, true_pred(), invariants_since_phase_V(rabbitmq), always(current_state_matches(rabbitmq)));
        }
    );
    assert_by(
        invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(invariants_since_phase_I(rabbitmq)).and(invariants_since_phase_II(rabbitmq)).and(invariants_since_phase_III(rabbitmq))
        .entails(
            true_pred().leads_to(always(current_state_matches(rabbitmq)))
        ),
        {
            let spec = invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(invariants_since_phase_I(rabbitmq)).and(invariants_since_phase_II(rabbitmq)).and(invariants_since_phase_III(rabbitmq));
            unpack_conditions_from_spec(spec, invariants_since_phase_IV(rabbitmq), true_pred(), always(current_state_matches(rabbitmq)));
            temp_pred_equality(true_pred().and(invariants_since_phase_IV(rabbitmq)), invariants_since_phase_IV(rabbitmq));
            helper_invariants::lemma_eventually_only_valid_stateful_set_exists(spec, rabbitmq);
            helper_invariants::lemma_eventually_only_valid_server_config_map_exists(spec, rabbitmq);
            leads_to_always_combine_temp(
                spec, true_pred(),
                lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(make_stateful_set_key(rabbitmq.object_ref()), rabbitmq)),
                lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(make_server_config_map_key(rabbitmq.object_ref()), rabbitmq))
            );
            leads_to_trans_temp(spec, true_pred(), invariants_since_phase_IV(rabbitmq), always(current_state_matches(rabbitmq)));
        }
    );
    assert_by(
        invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(invariants_since_phase_I(rabbitmq)).and(invariants_since_phase_II(rabbitmq)).entails(
            true_pred().leads_to(always(current_state_matches(rabbitmq)))
        ),
        {
            let spec = invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(invariants_since_phase_I(rabbitmq)).and(invariants_since_phase_II(rabbitmq));
            unpack_conditions_from_spec(spec, invariants_since_phase_III(rabbitmq), true_pred(), always(current_state_matches(rabbitmq)));
            temp_pred_equality(true_pred().and(invariants_since_phase_III(rabbitmq)), invariants_since_phase_III(rabbitmq));

            helper_invariants::lemma_true_leads_to_always_create_server_cm_req_msg_in_flight_implies_at_after_create_server_cm_step(spec, rabbitmq.object_ref());
            helper_invariants::lemma_true_leads_to_always_update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(spec, rabbitmq.object_ref());
            helper_invariants::lemma_true_leads_to_always_every_update_server_cm_req_does_the_same(spec, rabbitmq);
            helper_invariants::lemma_true_leads_to_always_every_create_server_cm_req_does_the_same(spec, rabbitmq);
            helper_invariants::lemma_true_leads_to_always_create_sts_req_msg_in_flight_implies_at_after_create_sts_step(spec, rabbitmq.object_ref());
            helper_invariants::lemma_true_leads_to_always_update_sts_req_msg_in_flight_implies_at_after_update_sts_step(spec, rabbitmq.object_ref());
            helper_invariants::lemma_true_leads_to_always_every_update_sts_req_does_the_same(spec, rabbitmq);
            helper_invariants::lemma_true_leads_to_always_every_create_sts_req_does_the_same(spec, rabbitmq);

            leads_to_always_combine_n!(
                spec, true_pred(),
                lift_state(helper_invariants::create_server_cm_req_msg_in_flight_implies_at_after_create_server_cm_step(rabbitmq.object_ref())),
                lift_state(helper_invariants::update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(rabbitmq.object_ref())),
                lift_state(helper_invariants::every_update_server_cm_req_does_the_same(rabbitmq)),
                lift_state(helper_invariants::every_create_server_cm_req_does_the_same(rabbitmq)),
                lift_state(helper_invariants::create_sts_req_msg_in_flight_implies_at_after_create_sts_step(rabbitmq.object_ref())),
                lift_state(helper_invariants::update_sts_req_msg_in_flight_implies_at_after_update_sts_step(rabbitmq.object_ref())),
                lift_state(helper_invariants::every_update_sts_req_does_the_same(rabbitmq)),
                lift_state(helper_invariants::every_create_sts_req_does_the_same(rabbitmq))
            );

            leads_to_trans_temp(spec, true_pred(), invariants_since_phase_III(rabbitmq), always(current_state_matches(rabbitmq)));
        }
    );
    assert_by(
        invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(invariants_since_phase_I(rabbitmq)).entails(
            true_pred().leads_to(always(current_state_matches(rabbitmq)))
        ),
        {
            let spec = invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(invariants_since_phase_I(rabbitmq));
            unpack_conditions_from_spec(spec, invariants_since_phase_II(rabbitmq), true_pred(), always(current_state_matches(rabbitmq)));
            temp_pred_equality(true_pred().and(invariants_since_phase_II(rabbitmq)), invariants_since_phase_II(rabbitmq));

            terminate::reconcile_eventually_terminates(spec, rabbitmq);
            RMQCluster::lemma_true_leads_to_always_the_object_in_reconcile_has_spec_and_uid_as(spec, rabbitmq);
            leads_to_trans_temp(spec, true_pred(), invariants_since_phase_II(rabbitmq), always(current_state_matches(rabbitmq)));
        }
    );

    // Now we eliminate the assumption []RMQCluster::crash_disabled() /\ []busy_disabled.
    assert_by(
        invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq))))
        .entails(
            true_pred().leads_to(always(current_state_matches(rabbitmq)))
        ),
        {
            let spec = invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq))));
            unpack_conditions_from_spec(spec, invariants_since_phase_I(rabbitmq), true_pred(), always(current_state_matches(rabbitmq)));
            temp_pred_equality(true_pred().and(invariants_since_phase_I(rabbitmq)), invariants_since_phase_I(rabbitmq));

            RMQCluster::lemma_true_leads_to_crash_always_disabled(spec);
            RMQCluster::lemma_true_leads_to_busy_always_disabled(spec);
            RMQCluster::lemma_true_leads_to_always_the_object_in_schedule_has_spec_and_uid_as(spec, rabbitmq);
            leads_to_always_combine_n!(
                spec,
                true_pred(),
                lift_state(RMQCluster::crash_disabled()),
                lift_state(RMQCluster::busy_disabled()),
                lift_state(RMQCluster::the_object_in_schedule_has_spec_and_uid_as(rabbitmq))
            );
            leads_to_trans_temp(spec, true_pred(), invariants_since_phase_I(rabbitmq), always(current_state_matches(rabbitmq)));
        }
    );

    // Then we unpack the assumption of []RMQCluster::desired_state_is(rabbitmq) from spec.
    assert_by(
        invariants(rabbitmq)
        .entails(
            always(lift_state(RMQCluster::desired_state_is(rabbitmq))).leads_to(always(current_state_matches(rabbitmq)))
        ),
        {
            let spec = invariants(rabbitmq);
            let assumption = always(lift_state(RMQCluster::desired_state_is(rabbitmq)));
            unpack_conditions_from_spec(spec, assumption, true_pred(), always(current_state_matches(rabbitmq)));
            temp_pred_equality(true_pred().and(assumption), assumption);
        }
    );

    entails_trans(
        cluster_spec().and(derived_invariants_since_beginning(rabbitmq)), invariants(rabbitmq),
        always(lift_state(RMQCluster::desired_state_is(rabbitmq))).leads_to(always(current_state_matches(rabbitmq)))
    );
    sm_spec_entails_all_invariants(rabbitmq);
    simplify_predicate(cluster_spec(), derived_invariants_since_beginning(rabbitmq));
}

proof fn sm_spec_entails_all_invariants(rabbitmq: RabbitmqClusterView)
    ensures
        cluster_spec().entails(derived_invariants_since_beginning(rabbitmq)),
{
    let spec = cluster_spec();
    RMQCluster::lemma_always_every_in_flight_msg_has_unique_id(spec);
    RMQCluster::lemma_always_each_resp_matches_at_most_one_pending_req(spec, rabbitmq.object_ref());
    RMQCluster::lemma_always_each_resp_if_matches_pending_req_then_no_other_resp_matches(spec, rabbitmq.object_ref());
    RMQCluster::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    RMQCluster::lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec);
    RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    helper_invariants::lemma_always_stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(spec, rabbitmq);
    helper_invariants::lemma_always_server_config_map_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(spec, rabbitmq);
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
        lift_state(RMQCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(make_stateful_set_key(rabbitmq.object_ref()), rabbitmq)),
        lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(make_server_config_map_key(rabbitmq.object_ref()), rabbitmq)),
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
        assumption_and_invariants_of_all_phases(rabbitmq)
        .entails(
            true_pred().leads_to(always(current_state_matches(rabbitmq)))
        ),
{
    let spec = assumption_and_invariants_of_all_phases(rabbitmq);

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

    lemma_from_after_get_server_config_map_to_rabbitmq_matches(rabbitmq);

    lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, rabbitmq, RabbitmqReconcileStep::AfterCreateServiceAccount, RabbitmqReconcileStep::AfterCreateRole);
    lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, rabbitmq, RabbitmqReconcileStep::AfterCreateRole, RabbitmqReconcileStep::AfterCreateRoleBinding);
    lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, rabbitmq, RabbitmqReconcileStep::AfterCreateRoleBinding, RabbitmqReconcileStep::AfterGetStatefulSet);

    lemma_from_after_get_stateful_set_to_rabbitmq_matches(rabbitmq);

    leads_to_trans_n!(
        spec,
        true_pred(),
        lift_state(|s: RMQCluster| { !s.ongoing_reconciles().contains_key(rabbitmq.object_ref()) }),
        lift_state(|s: RMQCluster| { !s.ongoing_reconciles().contains_key(rabbitmq.object_ref()) && s.scheduled_reconciles().contains_key(rabbitmq.object_ref())}),
        lift_state(no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateHeadlessService, rabbitmq)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateService, rabbitmq)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateErlangCookieSecret, rabbitmq)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateDefaultUserSecret, rabbitmq)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreatePluginsConfigMap, rabbitmq)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq))
    );
    leads_to_trans_temp(spec, true_pred(), lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)), lift_state(current_config_map_matches(rabbitmq)));

    lemma_server_config_map_is_stable(spec, rabbitmq, lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)));
    leads_to_trans_temp(
        spec, true_pred(),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)),
        always(lift_state(current_config_map_matches(rabbitmq)))
    );

    leads_to_trans_n!(
        spec,
        true_pred(),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServiceAccount, rabbitmq)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateRole, rabbitmq)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateRoleBinding, rabbitmq)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetStatefulSet, rabbitmq)),
        lift_state(current_stateful_set_matches(rabbitmq))
    );
    lemma_stateful_set_is_stable(spec, rabbitmq, lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetStatefulSet, rabbitmq)));
    leads_to_trans_temp(
        spec, true_pred(),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetStatefulSet, rabbitmq)),
        always(lift_state(current_stateful_set_matches(rabbitmq)))
    );

    leads_to_always_combine_temp(spec, true_pred(), lift_state(current_config_map_matches(rabbitmq)), lift_state(current_stateful_set_matches(rabbitmq)));
}

proof fn lemma_from_reconcile_idle_to_scheduled(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: RMQCluster| { !s.ongoing_reconciles().contains_key(rabbitmq.object_ref()) })
                .leads_to(lift_state(|s: RMQCluster| {
                    &&& !s.ongoing_reconciles().contains_key(rabbitmq.object_ref())
                    &&& s.scheduled_reconciles().contains_key(rabbitmq.object_ref())
                }))
        ),
{
    let pre = |s: RMQCluster| {
        &&& !s.ongoing_reconciles().contains_key(rabbitmq.object_ref())
        &&& !s.scheduled_reconciles().contains_key(rabbitmq.object_ref())
    };
    let post = |s: RMQCluster| {
        &&& !s.ongoing_reconciles().contains_key(rabbitmq.object_ref())
        &&& s.scheduled_reconciles().contains_key(rabbitmq.object_ref())
    };
    let input = rabbitmq.object_ref();

    RMQCluster::lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec(
        spec, input, RMQCluster::next(), RMQCluster::desired_state_is(rabbitmq), pre, post
    );
    valid_implies_implies_leads_to(spec, lift_state(post), lift_state(post));
    or_leads_to_combine(spec, pre, post, post);
    temp_pred_equality(lift_state(pre).or(lift_state(post)), lift_state(|s: RMQCluster| {!s.ongoing_reconciles().contains_key(rabbitmq.object_ref())}));
}

proof fn lemma_from_scheduled_to_init_step(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(RMQCluster::the_object_in_schedule_has_spec_and_uid_as(rabbitmq)))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: RMQCluster| {
                &&& !s.ongoing_reconciles().contains_key(rabbitmq.object_ref())
                &&& s.scheduled_reconciles().contains_key(rabbitmq.object_ref())
            })
                .leads_to(lift_state(no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init)))
        ),
{
    let pre = |s: RMQCluster| {
        &&& !s.ongoing_reconciles().contains_key(rabbitmq.object_ref())
        &&& s.scheduled_reconciles().contains_key(rabbitmq.object_ref())
    };
    let post = no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init);
    let input = (None, Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()(s)
        &&& RMQCluster::the_object_in_schedule_has_spec_and_uid_as(rabbitmq)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::the_object_in_schedule_has_spec_and_uid_as(rabbitmq))
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
    let input = (None, Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled())
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(input) => {
                if input.1.get_Some_0() != rabbitmq.object_ref() {
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
                let req_msg = ex.head().ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
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
                    &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
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
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage, step: RabbitmqReconcileStep
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
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id())
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && RMQCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = RMQCluster::transition_by_etcd(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
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
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, resp_msg: RMQMessage, step: RabbitmqReconcileStep, result_step: RabbitmqReconcileStep
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
    let input = (Some(resp_msg), Some(rabbitmq.object_ref()));

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

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref()))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(input) => {
                if input.1.is_Some() && input.1.get_Some_0() == rabbitmq.object_ref() {
                    assert(s_prime.ongoing_reconciles()[rabbitmq.object_ref()].local_state.reconcile_step == result_step);
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


}
