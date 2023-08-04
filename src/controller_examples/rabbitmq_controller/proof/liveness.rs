// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
    controller::state_machine::*,
    kubernetes_api::state_machine::{
        handle_create_request, handle_get_request, handle_request, transition_by_etcd,
        update_is_noop,
    },
    message::*,
};
use crate::rabbitmq_controller::{
    common::*,
    proof::{common::*, safety, terminate},
    spec::{rabbitmqcluster::*, reconciler::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// The current state matches the desired state described in the cr.
// I.e., the corresponding stateful set exists and its spec is the same as desired.
spec fn current_state_matches(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).is_Ok()
        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).get_Ok_0().data == make_server_config_map(rabbitmq).data
    }
}

// The liveness property says []desired_state_is(rabbitmq) ~> []current_state_matches(rabbitmq).
spec fn liveness(rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState>
    recommends
        rabbitmq.well_formed(),
{
    always(lift_state(RMQCluster::desired_state_is(rabbitmq))).leads_to(always(lift_state(current_state_matches(rabbitmq))))
}

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

// Next and all the wf conditions.
spec fn next_with_wf() -> TempPred<ClusterState> {
    always(lift_action(RMQCluster::next()))
    .and(tla_forall(|input| RMQCluster::kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::controller_next().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::schedule_controller_reconcile().weak_fairness(input)))
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
    RMQCluster::action_weak_fairness_is_stable(RMQCluster::disable_crash());
    RMQCluster::action_weak_fairness_is_stable(RMQCluster::disable_busy());
    stable_and_n!(
        always(lift_action(RMQCluster::next())),
        tla_forall(|input| RMQCluster::kubernetes_api_next().weak_fairness(input)),
        tla_forall(|input| RMQCluster::controller_next().weak_fairness(input)),
        tla_forall(|input| RMQCluster::schedule_controller_reconcile().weak_fairness(input)),
        RMQCluster::disable_crash().weak_fairness(()),
        RMQCluster::disable_busy().weak_fairness(())
    );
}

// All assumptions that makes liveness possible, such as controller crash no longer happens,
// the cr's spec always remains unchanged, and so on.
spec fn assumptions(rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    always(lift_state(RMQCluster::crash_disabled()))
    .and(always(lift_state(RMQCluster::busy_disabled())))
    .and(always(lift_state(RMQCluster::desired_state_is(rabbitmq))))
    .and(always(lift_state(RMQCluster::the_object_in_schedule_has_spec_as(rabbitmq))))
    .and(always(lift_state(RMQCluster::the_object_in_reconcile_has_spec_as(rabbitmq))))
}

proof fn assumptions_is_stable(rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(assumptions(rabbitmq))),
{
    stable_and_always_n!(
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::desired_state_is(rabbitmq)),
        lift_state(RMQCluster::the_object_in_schedule_has_spec_as(rabbitmq)),
        lift_state(RMQCluster::the_object_in_reconcile_has_spec_as(rabbitmq))
    );
}

// The safety invariants that are required to prove liveness.
spec fn invariants(rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref()))))
    .and(always(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref()))))
    .and(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed())))
    .and(always(lift_state(RMQCluster::each_scheduled_key_is_consistent_with_its_object())))
    .and(always(lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object())))
    .and(always(lift_state(safety::pending_msg_at_after_create_server_config_map_step_is_create_cm_req(rabbitmq.object_ref()))))
    .and(always(lift_state(safety::pending_msg_at_after_update_server_config_map_step_is_update_cm_req(rabbitmq.object_ref()))))
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
        valid(stable(invariants(rabbitmq))),
{
    stable_and_always_n!(
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())),
        lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(RMQCluster::each_scheduled_key_is_consistent_with_its_object()),
        lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()),
        lift_state(safety::pending_msg_at_after_create_server_config_map_step_is_create_cm_req(rabbitmq.object_ref())),
        lift_state(safety::pending_msg_at_after_update_server_config_map_step_is_update_cm_req(rabbitmq.object_ref())),
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

// Some other invariants requires to prove liveness.
// Note that different from the above invariants, these do not hold for the entire execution from init.
// They only hold since some point (e.g., when the rest id counter is the same as rest_id).
// Some of these invariants are also based on the assumptions.
spec fn invariants_since_rest_id(rabbitmq: RabbitmqClusterView, rest_id: RestId) -> TempPred<ClusterState> {
    always(lift_state(RMQCluster::rest_id_counter_is_no_smaller_than(rest_id)))
    .and(always(lift_state(safety::at_most_one_create_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))))
    .and(always(lift_state(safety::at_most_one_update_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))))
    .and(always(lift_state(safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))))
    .and(always(lift_state(safety::every_update_cm_req_since_rest_id_does_the_same(rabbitmq, rest_id))))
}

proof fn invariants_since_rest_id_is_stable(rabbitmq: RabbitmqClusterView, rest_id: RestId)
    ensures
        valid(stable(invariants_since_rest_id(rabbitmq, rest_id))),
{
    stable_and_always_n!(
        lift_state(RMQCluster::rest_id_counter_is_no_smaller_than(rest_id)),
        lift_state(safety::at_most_one_create_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)),
        lift_state(safety::at_most_one_update_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)),
        lift_state(safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)),
        lift_state(safety::every_update_cm_req_since_rest_id_does_the_same(rabbitmq, rest_id))
    );
}

// This invariant is also used to prove liveness.
// Different from above, it only holds after some time since the rest id counter is the same as rest_id.
spec fn invariants_led_to_by_rest_id(rabbitmq: RabbitmqClusterView, rest_id: RestId) -> TempPred<ClusterState> {
    always(lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)))
}

proof fn liveness_proof(rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
    ensures
        cluster_spec().entails(liveness(rabbitmq)),
{
    lemma_true_leads_to_always_current_state_matches_rabbitmq(rabbitmq);
    // Then prove that with all the invariants and the base assumptions (i.e., controller does not crash and cr.spec remains unchanged)
    // true leads to []current_state_matches(rabbitmq).
    // This is done by eliminating the other assumptions derived from the base assumptions using the unpack rule.
    assert_by(
        next_with_wf().and(invariants(rabbitmq)).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq))))
        .and(always(lift_state(RMQCluster::crash_disabled()))).and(always(lift_state(RMQCluster::busy_disabled())))
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(rabbitmq))))
        ),
        {
            let spec = next_with_wf().and(invariants(rabbitmq)).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(always(lift_state(RMQCluster::crash_disabled()))).and(always(lift_state(RMQCluster::busy_disabled())));
            let other_assumptions = always(lift_state(RMQCluster::the_object_in_schedule_has_spec_as(rabbitmq)))
                .and(always(lift_state(RMQCluster::the_object_in_reconcile_has_spec_as(rabbitmq))));
            temp_pred_equality(
                next_with_wf().and(invariants(rabbitmq)).and(assumptions(rabbitmq)),
                next_with_wf().and(invariants(rabbitmq)).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq))))
                .and(always(lift_state(RMQCluster::crash_disabled()))).and(always(lift_state(RMQCluster::busy_disabled()))).and(other_assumptions)
            );
            assert_by(
                valid(stable(spec)),
                {
                    next_with_wf_is_stable();
                    invariants_is_stable(rabbitmq);
                    always_p_is_stable(lift_state(RMQCluster::desired_state_is(rabbitmq)));
                    always_p_is_stable(lift_state(RMQCluster::crash_disabled()));
                    always_p_is_stable(lift_state(RMQCluster::busy_disabled()));

                    stable_and_n!(
                        next_with_wf(),
                        invariants(rabbitmq),
                        always(lift_state(RMQCluster::desired_state_is(rabbitmq))),
                        always(lift_state(RMQCluster::crash_disabled())),
                        always(lift_state(RMQCluster::busy_disabled()))
                    );
                }
            );
            unpack_conditions_from_spec(spec, other_assumptions, true_pred(), always(lift_state(current_state_matches(rabbitmq))));
            temp_pred_equality(true_pred().and(other_assumptions), other_assumptions);

            terminate::reconcile_eventually_terminates(spec, rabbitmq);
            RMQCluster::lemma_true_leads_to_always_the_object_in_schedule_has_spec_as(spec, rabbitmq);
            RMQCluster::lemma_true_leads_to_always_the_object_in_reconcile_has_spec_as(spec, rabbitmq);

            leads_to_always_combine_n!(
                spec, true_pred(),
                lift_state(RMQCluster::the_object_in_schedule_has_spec_as(rabbitmq)),
                lift_state(RMQCluster::the_object_in_reconcile_has_spec_as(rabbitmq))
            );

            always_and_equality_n!(
                lift_state(RMQCluster::the_object_in_schedule_has_spec_as(rabbitmq)),
                lift_state(RMQCluster::the_object_in_reconcile_has_spec_as(rabbitmq))
            );

            leads_to_trans_temp(spec, true_pred(), other_assumptions, always(lift_state(current_state_matches(rabbitmq))));
        }
    );

    // Now we eliminate the assumption []RMQCluster::crash_disabled() /\ []busy_disabled.
    assert_by(
        next_with_wf().and(invariants(rabbitmq)).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq))))
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(rabbitmq))))
        ),
        {
            let spec = next_with_wf().and(invariants(rabbitmq)).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq))));
            assert_by(
                valid(stable(spec)),
                {
                    next_with_wf_is_stable();
                    invariants_is_stable(rabbitmq);
                    always_p_is_stable(lift_state(RMQCluster::desired_state_is(rabbitmq)));

                    stable_and_n!(
                        next_with_wf(),
                        invariants(rabbitmq),
                        always(lift_state(RMQCluster::desired_state_is(rabbitmq)))
                    );
                }
            );
            temp_pred_equality(
                spec.and(always(lift_state(RMQCluster::crash_disabled())).and(always(lift_state(RMQCluster::busy_disabled())))),
                spec.and(always(lift_state(RMQCluster::crash_disabled()))).and(always(lift_state(RMQCluster::busy_disabled())))
            );
            unpack_conditions_from_spec(spec, always(lift_state(RMQCluster::crash_disabled())).and(always(lift_state(RMQCluster::busy_disabled()))), true_pred(), always(lift_state(current_state_matches(rabbitmq))));
            temp_pred_equality(
                true_pred().and(always(lift_state(RMQCluster::crash_disabled())).and(always(lift_state(RMQCluster::busy_disabled())))),
                always(lift_state(RMQCluster::crash_disabled())).and(always(lift_state(RMQCluster::busy_disabled())))
            );

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
            leads_to_trans_temp(spec, true_pred(), always(lift_state(RMQCluster::crash_disabled())).and(always(lift_state(RMQCluster::busy_disabled()))), always(lift_state(current_state_matches(rabbitmq))));
        }
    );

    // Then we unpack the assumption of []RMQCluster::desired_state_is(rabbitmq) from spec.
    assert_by(
        next_with_wf().and(invariants(rabbitmq))
        .entails(
            always(lift_state(RMQCluster::desired_state_is(rabbitmq))).leads_to(always(lift_state(current_state_matches(rabbitmq))))
        ),
        {
            let spec = next_with_wf().and(invariants(rabbitmq));
            let assumption = always(lift_state(RMQCluster::desired_state_is(rabbitmq)));
            assert_by(
                valid(stable(spec)),
                {
                    next_with_wf_is_stable();
                    invariants_is_stable(rabbitmq);

                    stable_and_n!(next_with_wf(), invariants(rabbitmq));
                }
            );
            unpack_conditions_from_spec(spec, assumption, true_pred(), always(lift_state(current_state_matches(rabbitmq))));
            temp_pred_equality(true_pred().and(assumption), assumption);
        }
    );

    entails_trans(
        cluster_spec().and(invariants(rabbitmq)), next_with_wf().and(invariants(rabbitmq)),
        always(lift_state(RMQCluster::desired_state_is(rabbitmq))).leads_to(always(lift_state(current_state_matches(rabbitmq))))
    );
    sm_spec_entails_all_invariants(rabbitmq);
    simplify_predicate(cluster_spec(), invariants(rabbitmq));
}

proof fn sm_spec_entails_all_invariants(rabbitmq: RabbitmqClusterView)
    ensures
        cluster_spec().entails(invariants(rabbitmq)),
{
    let spec = cluster_spec();
    RMQCluster::lemma_always_every_in_flight_msg_has_unique_id();
    RMQCluster::lemma_always_each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref());
    RMQCluster::lemma_always_each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref());
    RMQCluster::lemma_always_every_in_flight_msg_has_lower_id_than_allocator();
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    RMQCluster::lemma_always_each_scheduled_key_is_consistent_with_its_object(spec);
    RMQCluster::lemma_always_each_key_in_reconcile_is_consistent_with_its_object(spec);
    safety::lemma_always_pending_msg_at_after_create_server_config_map_step_is_create_cm_req(spec, rabbitmq.object_ref());
    safety::lemma_always_pending_msg_at_after_update_server_config_map_step_is_update_cm_req(spec, rabbitmq.object_ref());
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
        lift_state(safety::pending_msg_at_after_create_server_config_map_step_is_create_cm_req(rabbitmq.object_ref())),
        lift_state(safety::pending_msg_at_after_update_server_config_map_step_is_update_cm_req(rabbitmq.object_ref())),
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

proof fn lemma_true_leads_to_always_current_state_matches_rabbitmq(rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
    ensures
        next_with_wf().and(invariants(rabbitmq)).and(assumptions(rabbitmq))
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(rabbitmq))))
        ),
{
    let spec = next_with_wf().and(invariants(rabbitmq)).and(assumptions(rabbitmq));
    assert forall |rest_id| spec.entails(
        lift_state(#[trigger] RMQCluster::rest_id_counter_is(rest_id)).leads_to(always(lift_state(current_state_matches(rabbitmq))))
    ) by {
        lemma_some_rest_id_leads_to_always_current_state_matches_rabbitmq(rabbitmq, rest_id);
    }
    let has_rest_id = |rest_id| lift_state(RMQCluster::rest_id_counter_is(rest_id));
    leads_to_exists_intro(spec, has_rest_id, always(lift_state(current_state_matches(rabbitmq))));
    assert_by(
        tla_exists(has_rest_id) == true_pred::<ClusterState>(),
        {
            assert forall |ex| #[trigger] true_pred::<ClusterState>().satisfied_by(ex)
            implies tla_exists(has_rest_id).satisfied_by(ex) by {
                let rest_id = ex.head().rest_id_allocator.rest_id_counter;
                assert(has_rest_id(rest_id).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(has_rest_id), true_pred::<ClusterState>());
        }
    );
}

proof fn lemma_some_rest_id_leads_to_always_current_state_matches_rabbitmq(rabbitmq: RabbitmqClusterView, rest_id: RestId)
    requires
        rabbitmq.well_formed(),
    ensures
        next_with_wf().and(invariants(rabbitmq)).and(assumptions(rabbitmq))
        .entails(
            lift_state(RMQCluster::rest_id_counter_is(rest_id)).leads_to(always(lift_state(current_state_matches(rabbitmq))))
        ),
{
    let spec = next_with_wf().and(invariants(rabbitmq)).and(assumptions(rabbitmq));
    let spec_with_rest_id = spec.and(lift_state(RMQCluster::rest_id_counter_is(rest_id)));
    next_with_wf_is_stable();
    invariants_is_stable(rabbitmq);
    assumptions_is_stable(rabbitmq);
    // To prove the liveness, we need some extra invariants (invariants_since_rest_id and invariants_led_to_by_rest_id)
    // that only holds since the rest id counter is rest_id.
    assert_by(
        spec_with_rest_id.and(invariants_since_rest_id(rabbitmq, rest_id)).entails(
            invariants_led_to_by_rest_id(rabbitmq, rest_id).leads_to(always(lift_state(current_state_matches(rabbitmq))))
        ),
        {
            lemma_true_leads_to_always_current_state_matches_rabbitmq_under_eventual_invariants(rabbitmq, rest_id);
            invariants_since_rest_id_is_stable(rabbitmq, rest_id);
            stable_and_n!(next_with_wf(), invariants(rabbitmq), assumptions(rabbitmq), invariants_since_rest_id(rabbitmq, rest_id));
            unpack_conditions_from_spec(
                spec.and(invariants_since_rest_id(rabbitmq, rest_id)),
                invariants_led_to_by_rest_id(rabbitmq, rest_id),
                true_pred(),
                always(lift_state(current_state_matches(rabbitmq)))
            );
            temp_pred_equality(
                true_pred().and(invariants_led_to_by_rest_id(rabbitmq, rest_id)),
                invariants_led_to_by_rest_id(rabbitmq, rest_id)
            );
            entails_trans(
                spec_with_rest_id.and(invariants_since_rest_id(rabbitmq, rest_id)),
                spec.and(invariants_since_rest_id(rabbitmq, rest_id)),
                invariants_led_to_by_rest_id(rabbitmq, rest_id).leads_to(always(lift_state(current_state_matches(rabbitmq))))
            );
        }
    );

    RMQCluster::lemma_true_leads_to_always_no_req_before_rest_id_is_in_flight(
        spec_with_rest_id.and(invariants_since_rest_id(rabbitmq, rest_id)), rest_id
    );

    // Here we eliminate invariants_led_to_by_rest_id using leads_to_trans_temp
    leads_to_trans_temp(spec_with_rest_id.and(invariants_since_rest_id(rabbitmq, rest_id)), true_pred(), invariants_led_to_by_rest_id(rabbitmq, rest_id), always(lift_state(current_state_matches(rabbitmq))));

    assert_by(
        spec_with_rest_id.entails(invariants_since_rest_id(rabbitmq, rest_id)),
        {
            eliminate_always(spec_with_rest_id, lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()));
            eliminate_always(spec_with_rest_id, lift_state(safety::pending_msg_at_after_create_server_config_map_step_is_create_cm_req(rabbitmq.object_ref())));
            eliminate_always(spec_with_rest_id, lift_state(safety::pending_msg_at_after_update_server_config_map_step_is_update_cm_req(rabbitmq.object_ref())));

            RMQCluster::lemma_always_rest_id_counter_is_no_smaller_than(spec_with_rest_id, rest_id);
            safety::lemma_always_at_most_one_create_cm_req_since_rest_id_is_in_flight(spec_with_rest_id, rabbitmq.object_ref(), rest_id);
            safety::lemma_always_at_most_one_update_cm_req_since_rest_id_is_in_flight(spec_with_rest_id, rabbitmq.object_ref(), rest_id);
            safety::lemma_always_no_delete_cm_req_since_rest_id_is_in_flight(spec_with_rest_id, rabbitmq.object_ref(), rest_id);
            safety::lemma_always_every_update_cm_req_since_rest_id_does_the_same(spec_with_rest_id, rabbitmq, rest_id);

            entails_and_n!(
                spec_with_rest_id,
                always(lift_state(RMQCluster::rest_id_counter_is_no_smaller_than(rest_id))),
                always(lift_state(safety::at_most_one_create_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))),
                always(lift_state(safety::at_most_one_update_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))),
                always(lift_state(safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))),
                always(lift_state(safety::every_update_cm_req_since_rest_id_does_the_same(rabbitmq, rest_id)))
            );
        }
    );

    // And we eliminate invariants_since_rest_id using simplify_predicate.
    simplify_predicate(spec_with_rest_id, invariants_since_rest_id(rabbitmq, rest_id));
    stable_and_n!(next_with_wf(), invariants(rabbitmq), assumptions(rabbitmq));
    unpack_conditions_from_spec(spec, lift_state(RMQCluster::rest_id_counter_is(rest_id)), true_pred(), always(lift_state(current_state_matches(rabbitmq))));
    temp_pred_equality::<ClusterState>(
        true_pred().and(lift_state(RMQCluster::rest_id_counter_is(rest_id))),
        lift_state(RMQCluster::rest_id_counter_is(rest_id))
    );
}

// This lemma proves that with all the invariants, assumptions, and even invariants that only hold since rest id counter is rest_id,
// true ~> []current_state_matches(rabbitmq).
proof fn lemma_true_leads_to_always_current_state_matches_rabbitmq_under_eventual_invariants(rabbitmq: RabbitmqClusterView, rest_id: RestId)
    requires
        rabbitmq.well_formed(),
    ensures
        next_with_wf()
        .and(invariants(rabbitmq))
        .and(assumptions(rabbitmq))
        .and(invariants_since_rest_id(rabbitmq, rest_id))
        .and(invariants_led_to_by_rest_id(rabbitmq, rest_id))
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(rabbitmq))))
        ),
{
    let spec = next_with_wf().and(invariants(rabbitmq)).and(assumptions(rabbitmq))
            .and(invariants_since_rest_id(rabbitmq, rest_id)).and(invariants_led_to_by_rest_id(rabbitmq, rest_id));

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
    lemma_from_after_get_server_config_map_to_rabbitmq_matches(rabbitmq, rest_id);

    leads_to_trans_n!(
        spec,
        true_pred(),
        lift_state(|s: ClusterState| { !s.reconcile_state_contains(rabbitmq.object_ref()) }),
        lift_state(|s: ClusterState| { !s.reconcile_state_contains(rabbitmq.object_ref()) && s.reconcile_scheduled_for(rabbitmq.object_ref())}),
        lift_state(no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateHeadlessService, rabbitmq, arbitrary())),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateService, rabbitmq, arbitrary())),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateErlangCookieSecret, rabbitmq, arbitrary())),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateDefaultUserSecret, rabbitmq, arbitrary())),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreatePluginsConfigMap, rabbitmq, arbitrary())),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, arbitrary())),
        lift_state(current_state_matches(rabbitmq))
    );

    lemma_server_config_map_is_stable(
        spec, rabbitmq, rest_id,
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, arbitrary()))
    );
    leads_to_trans_temp(
        spec, true_pred(),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, arbitrary())),
        always(lift_state(current_state_matches(rabbitmq)))
    );
}

proof fn lemma_from_reconcile_idle_to_scheduled(spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: ClusterState| { !s.reconcile_state_contains(rabbitmq.object_ref()) })
                .leads_to(lift_state(|s: ClusterState| {
                    &&& !s.reconcile_state_contains(rabbitmq.object_ref())
                    &&& s.reconcile_scheduled_for(rabbitmq.object_ref())
                }))
        ),
{
    let pre = |s: ClusterState| {
        &&& !s.reconcile_state_contains(rabbitmq.object_ref())
        &&& !s.reconcile_scheduled_for(rabbitmq.object_ref())
    };
    let post = |s: ClusterState| {
        &&& !s.reconcile_state_contains(rabbitmq.object_ref())
        &&& s.reconcile_scheduled_for(rabbitmq.object_ref())
    };
    let input = rabbitmq.object_ref();

    RMQCluster::lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec(
        spec, input, RMQCluster::next(), RMQCluster::desired_state_is(rabbitmq), pre, post
    );
    valid_implies_implies_leads_to(spec, lift_state(post), lift_state(post));
    or_leads_to_combine(spec, pre, post, post);
    temp_pred_equality(lift_state(pre).or(lift_state(post)), lift_state(|s: ClusterState| {!s.reconcile_state_contains(rabbitmq.object_ref())}));
}

proof fn lemma_from_scheduled_to_init_step(spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_scheduled_key_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(RMQCluster::the_object_in_schedule_has_spec_as(rabbitmq)))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: ClusterState| {
                &&& !s.reconcile_state_contains(rabbitmq.object_ref())
                &&& s.reconcile_scheduled_for(rabbitmq.object_ref())
            })
                .leads_to(lift_state(no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init)))
        ),
{
    let pre = |s: ClusterState| {
        &&& !s.reconcile_state_contains(rabbitmq.object_ref())
        &&& s.reconcile_scheduled_for(rabbitmq.object_ref())
    };
    let post = no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init);
    let input = (Option::None, Option::None, Option::Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::each_scheduled_key_is_consistent_with_its_object()(s)
        &&& RMQCluster::the_object_in_schedule_has_spec_as(rabbitmq)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::each_scheduled_key_is_consistent_with_its_object()),
        lift_state(RMQCluster::the_object_in_schedule_has_spec_as(rabbitmq))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
        .and(lift_state(RMQCluster::each_scheduled_key_is_consistent_with_its_object()))
        .and(lift_state(RMQCluster::the_object_in_schedule_has_spec_as(rabbitmq)))
    );

    RMQCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next,
        RMQCluster::run_scheduled_reconcile(), pre, post
    );
}

proof fn lemma_from_init_step_to_after_create_headless_service_step(
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init))
                .leads_to(lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateHeadlessService, rabbitmq, arbitrary())))
        ),
{
    let pre = no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init);
    let post = pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateHeadlessService, rabbitmq, arbitrary());
    let input = (Option::None, Option::None, Option::Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
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

    RMQCluster::lemma_pre_leads_to_post_by_controller( spec, input, stronger_next, RMQCluster::continue_reconcile(), pre, post);
}

// This lemma ensures that rabbitmq controller at some step with pending request in flight will finally enter its next step.
// For step and next_step, they both require the reconcile_state to have a pending request which is the correct request for that step.
// Note that in this lemma we add some constraints to step:
//    1. There is only one possible next_step for it.
//    2. When the controller enters this step, it must create a request (which is piggybacked by the pending request message)
// We don't care about update step here, so arbitraray() is used to show that the object parameter in
// pending_req_in_flight_at_rabbitmq_step_with_rabbitmq is unrelated.
proof fn lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, step: RabbitmqReconcileStep, next_step: RabbitmqReconcileStep
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
        // next_step != RabbitmqReconcileStep::Init,
        forall |rabbitmq_1, resp_o|
            #[trigger] reconcile_core(rabbitmq_1, resp_o, RabbitmqReconcileState{ reconcile_step: step }).0.reconcile_step == next_step
            && reconcile_core(rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).1.is_Some()
            && reconcile_core(rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).1.get_Some_0().is_KRequest()
            && (rabbitmq_1.object_ref() == rabbitmq.object_ref() && rabbitmq_1.spec == rabbitmq.spec ==>
            forall |object: DynamicObjectView| #[trigger] is_correct_pending_request_at_rabbitmq_step(
                next_step, reconcile_core(rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).1.get_Some_0().get_KRequest_0(), rabbitmq, object
            )),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, arbitrary()))
            .leads_to(lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(next_step, rabbitmq, arbitrary())))
        ),
{
    // The proof of this lemma contains of two parts (two leads_to's) and then a leads_to_trans:
    //     1. at_step(step) /\ pending_request in flight /\ correct_request ~>
    //                         at_step(step) /\ response in flight /\ match(response, pending_request)
    //     2. at_step(step) /\ response in flight /\ match(response, pending_request) ~>
    //                         at_step(next_step) /\ pending_request in flight /\ correct_request
    // This predicate is used to give a specific request for the pre state for using wf1 which requires an input.
    let pre_and_req_in_flight = |req_msg| lift_state(
        req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, req_msg, arbitrary())
    );
    // This predicate is the intermediate state of the two leads_to
    let pre_and_exists_resp_in_flight = lift_state(
        exists_resp_in_flight_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, arbitrary())
    );
    // This predicate is used to give a specific request for the intermediate state for using wf1 which requires an input.
    let pre_and_resp_in_flight = |resp_msg| lift_state(
        resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, resp_msg, arbitrary())
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
        tla_exists(pre_and_req_in_flight) == lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, arbitrary())),
        {
            assert forall |ex|
                #[trigger] lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, arbitrary())).satisfied_by(ex)
            implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().pending_req_of(rabbitmq.object_ref());
                assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(
                tla_exists(pre_and_req_in_flight),
                lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, arbitrary()))
            );
        }
    );
    // Similarly we eliminate resp_msg using leads_to_exists_intro.
    assert forall |resp_msg|
        spec.entails(
            #[trigger] pre_and_resp_in_flight(resp_msg)
                .leads_to(lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(next_step, rabbitmq, arbitrary())))
        )
    by {
        lemma_from_resp_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, rabbitmq, resp_msg, step, next_step);
    }
    leads_to_exists_intro(
        spec,
        pre_and_resp_in_flight,
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(next_step, rabbitmq, arbitrary()))
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
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, arbitrary())),
        pre_and_exists_resp_in_flight,
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(next_step, rabbitmq, arbitrary()))
    );
}

proof fn lemma_receives_some_resp_at_rabbitmq_step_with_rabbitmq(
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, req_msg: Message, step: RabbitmqReconcileStep
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
            lift_state(req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, req_msg, arbitrary()))
                .leads_to(lift_state(exists_resp_in_flight_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, arbitrary())))
        ),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, req_msg, arbitrary());
    let post = exists_resp_in_flight_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, arbitrary());
    let input = Option::Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
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
        let resp_msg = transition_by_etcd(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        });
    }

    RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, handle_request(), pre, post
    );
}

// This lemma ensures that rabbitmq controller at some step with a response in flight that matches its pending request will finally enter its next step.
// For step and next_step, they both require the reconcile_state to have a pending request which is the correct request
// for that step. For step alone, there is a known response (the parameter resp_msg) in flight that matches the pending request.
// Note that in this lemma we add some constraints to step:
//    1. There is only one possible next_step for it.
//    2. When the controller enters this step, it must creates a request (which will be used to create the pending request message)
// We don't care about update step here, so arbitraray() is used to show that the object parameter in
// pending_req_in_flight_at_rabbitmq_step_with_rabbitmq is unrelated.
proof fn lemma_from_resp_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, resp_msg: Message, step: RabbitmqReconcileStep, result_step: RabbitmqReconcileStep
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        step != RabbitmqReconcileStep::Done, step != RabbitmqReconcileStep::Error,
        // result_step != RabbitmqReconcileStep::Init,
        // This forall rabbitmq_1 constraint is used because the cr passed to reconcile_core is not necessarily rabbitmq here.
        // We only know that rabbitmq_1.object_ref() == rabbitmq.object_ref() && rabbitmq_1.spec == rabbitmq.spec.
        forall |rabbitmq_1, resp_o|
            #[trigger] reconcile_core(rabbitmq_1, resp_o, RabbitmqReconcileState{ reconcile_step: step }).0.reconcile_step == result_step
            && reconcile_core(rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).1.is_Some()
            && reconcile_core(rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).1.get_Some_0().is_KRequest()
            && (rabbitmq_1.object_ref() == rabbitmq.object_ref() && rabbitmq_1.spec == rabbitmq.spec ==>
            forall |object: DynamicObjectView| #[trigger] is_correct_pending_request_at_rabbitmq_step(
                result_step, reconcile_core(rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).1.get_Some_0().get_KRequest_0(), rabbitmq, object
            )),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, resp_msg, arbitrary()))
                .leads_to(lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(result_step, rabbitmq, arbitrary())))
        ),
{
    let pre = resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(step, rabbitmq, resp_msg, arbitrary());
    let post = pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(result_step, rabbitmq, arbitrary());
    let input = (Option::Some(resp_msg), Option::None, Option::Some(rabbitmq.object_ref()));

    // For every part of stronger_next:
    //   - next(): the next predicate of the state machine
    //   - RMQCluster::crash_disabled(): to ensure that the reconcile process can continue
    //   - RMQCluster::busy_disabled(): to ensure that the request will get its expected response
    //    (Note that this is not required for termination)
    //   - each_resp_matches_at_most_one_pending_req: to make sure that the resp_msg will not be used by other cr
    let stronger_next = |s, s_prime: ClusterState| {
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

    RMQCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next,
        RMQCluster::continue_reconcile(), pre, post
    );
}

proof fn lemma_from_after_get_server_config_map_to_rabbitmq_matches(rabbitmq: RabbitmqClusterView, rest_id: nat)
    requires
        rabbitmq.well_formed(),
    ensures
        next_with_wf()
        .and(invariants(rabbitmq))
        .and(assumptions(rabbitmq))
        .and(invariants_since_rest_id(rabbitmq, rest_id))
        .and(invariants_led_to_by_rest_id(rabbitmq, rest_id))
        .entails(
            lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, arbitrary())).leads_to(lift_state(current_state_matches(rabbitmq)))
        ),
{
    let spec = next_with_wf().and(invariants(rabbitmq)).and(assumptions(rabbitmq))
    .and(invariants_since_rest_id(rabbitmq, rest_id)).and(invariants_led_to_by_rest_id(rabbitmq, rest_id));
    lemma_from_after_get_server_config_map_and_key_not_exists_to_rabbitmq_matches(rabbitmq, rest_id);
    lemma_from_after_get_server_config_map_and_key_exists_to_rabbitmq_matches(rabbitmq, rest_id);
    let key_not_exists = |s: ClusterState| {
            &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, arbitrary())(s)
    };
    let key_exists = |s: ClusterState| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, arbitrary())(s)
    };
    or_leads_to_combine(spec, key_not_exists, key_exists, current_state_matches(rabbitmq));
    temp_pred_equality(
        lift_state(key_not_exists).or(lift_state(key_exists)),
        lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, arbitrary()))
    );
}

proof fn lemma_from_after_get_server_config_map_and_key_not_exists_to_rabbitmq_matches(rabbitmq: RabbitmqClusterView, rest_id: nat)
    requires
        rabbitmq.well_formed(),
    ensures
        next_with_wf()
        .and(invariants(rabbitmq))
        .and(assumptions(rabbitmq))
        .and(invariants_since_rest_id(rabbitmq, rest_id))
        .and(invariants_led_to_by_rest_id(rabbitmq, rest_id))
        .entails(
            lift_state(|s: ClusterState| {
                &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, arbitrary())(s)
            }).leads_to(lift_state(current_state_matches(rabbitmq)))
        ),
{
    let spec = next_with_wf().and(invariants(rabbitmq)).and(assumptions(rabbitmq))
    .and(invariants_since_rest_id(rabbitmq, rest_id)).and(invariants_led_to_by_rest_id(rabbitmq, rest_id));
    let pre = lift_state(|s: ClusterState| {
        &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, arbitrary())(s)
    });
    let post = lift_state(|s: ClusterState| {
        &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServerConfigMap, rabbitmq, arbitrary())(s)
    });
    let pre_and_req_in_flight = |req_msg| lift_state(
        |s: ClusterState| {
            &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, req_msg, arbitrary())(s)
        }
    );
    let pre_and_exists_resp_in_flight = lift_state(
        |s: ClusterState| {
            &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& at_after_get_server_config_map_step_with_rabbitmq_and_exists_not_found_resp_in_flight(rabbitmq)(s)
        }
    );
    let pre_and_resp_in_flight = |resp_msg| lift_state(
        |s: ClusterState| {
            &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, resp_msg, arbitrary())(s)
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    );
    let post_and_req_in_flight = |req_msg| lift_state(
        |s: ClusterState| {
            &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServerConfigMap, rabbitmq, req_msg, arbitrary())(s)
        }
    );
    assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight))
    by {
        lemma_receives_not_found_resp_at_after_get_server_config_map_step_with_rabbitmq(spec, rabbitmq, rest_id, req_msg);
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
        lemma_from_after_get_server_config_map_step_to_after_create_server_config_map_step(spec, rabbitmq, rest_id, resp_msg);
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

    assert forall |req_msg| spec.entails(#[trigger] post_and_req_in_flight(req_msg).leads_to(lift_state(current_state_matches(rabbitmq))))
    by {
        lemma_cm_is_created_at_after_create_server_config_map_step_with_rabbitmq(spec, rabbitmq, rest_id, req_msg);
    }
    leads_to_exists_intro(spec, post_and_req_in_flight, lift_state(current_state_matches(rabbitmq)));
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
    leads_to_trans_temp(spec, pre, post, lift_state(current_state_matches(rabbitmq)));
}

proof fn lemma_receives_not_found_resp_at_after_get_server_config_map_step_with_rabbitmq(
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, rest_id: nat, req_msg: Message
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(safety::at_most_one_create_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                    &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, req_msg, arbitrary())(s)
                }
            )
                .leads_to(lift_state(
                    |s: ClusterState| {
                        &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                        &&& at_after_get_server_config_map_step_with_rabbitmq_and_exists_not_found_resp_in_flight(rabbitmq)(s)
                    }
                ))
        ),
{
    let pre = |s: ClusterState| {
        &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, req_msg, arbitrary())(s)
    };
    let post = |s: ClusterState| {
        &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& at_after_get_server_config_map_step_with_rabbitmq_and_exists_not_found_resp_in_flight(rabbitmq)(s)
    };
    let input = Option::Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& safety::at_most_one_create_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(safety::at_most_one_create_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
        .and(lift_state(RMQCluster::busy_disabled()))
        .and(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))
        .and(lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(safety::at_most_one_create_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = handle_get_request(req_msg, s.kubernetes_api_state).1;
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
        let resp_msg = handle_get_request(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        });
    }

    RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, handle_request(), pre, post
    );
}

proof fn lemma_from_after_get_server_config_map_step_to_after_create_server_config_map_step(
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, rest_id: nat, resp_msg: Message
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(safety::at_most_one_create_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: ClusterState| {
                &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                &&& resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, resp_msg, arbitrary())(s)
                &&& resp_msg.content.get_get_response().res.is_Err()
                &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
            })
                .leads_to(lift_state(|s: ClusterState| {
                    &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                    &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServerConfigMap, rabbitmq, arbitrary())(s)
                }))
        ),
{
    let pre = |s: ClusterState| {
        &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, resp_msg, arbitrary())(s)
        &&& resp_msg.content.get_get_response().res.is_Err()
        &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
    };
    let post = |s: ClusterState| {
        &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServerConfigMap, rabbitmq, arbitrary())(s)
    };
    let input = (Option::Some(resp_msg), Option::None, Option::Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())(s)
        &&& RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())(s)
        &&& RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& safety::at_most_one_create_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)(s)
    };

    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())),
        lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(safety::at_most_one_create_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
        .and(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))
        .and(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))
        .and(lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(safety::at_most_one_create_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))
    );

    RMQCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next,
        RMQCluster::continue_reconcile(), pre, post
    );
}

proof fn lemma_cm_is_created_at_after_create_server_config_map_step_with_rabbitmq(
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, rest_id: nat, req_msg: Message
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(safety::at_most_one_create_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                    &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServerConfigMap, rabbitmq, req_msg, arbitrary())(s)
                }
            )
                .leads_to(lift_state(
                    |s: ClusterState| {
                        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).is_Ok()
                        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).get_Ok_0().data == make_server_config_map(rabbitmq).data
                    }
                ))
        ),
{
    let pre = |s: ClusterState| {
        &&& !s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServerConfigMap, rabbitmq, req_msg, arbitrary())(s)
    };
    let post = |s: ClusterState| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).is_Ok()
        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).get_Ok_0().data == make_server_config_map(rabbitmq).data
    };
    let input = Option::Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& safety::at_most_one_create_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(safety::at_most_one_create_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
        .and(lift_state(RMQCluster::busy_disabled()))
        .and(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))
        .and(lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(safety::at_most_one_create_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))
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
        spec, input, stronger_next, handle_request(), pre, post
    );
}

proof fn lemma_from_after_get_server_config_map_and_key_exists_to_rabbitmq_matches(rabbitmq: RabbitmqClusterView, rest_id: nat)
    requires
        rabbitmq.well_formed(),
    ensures
        next_with_wf()
        .and(invariants(rabbitmq))
        .and(assumptions(rabbitmq))
        .and(invariants_since_rest_id(rabbitmq, rest_id))
        .and(invariants_led_to_by_rest_id(rabbitmq, rest_id))
        .entails(
            lift_state(|s: ClusterState| {
                &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, arbitrary())(s)
            }).leads_to(lift_state(current_state_matches(rabbitmq)))
        ),
{
    let spec = next_with_wf().and(invariants(rabbitmq)).and(assumptions(rabbitmq))
    .and(invariants_since_rest_id(rabbitmq, rest_id)).and(invariants_led_to_by_rest_id(rabbitmq, rest_id));
    let pre = lift_state(|s: ClusterState| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, arbitrary())(s)
    });
    let pre_with_object = |object| lift_state(
        |s: ClusterState| {
            &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
            &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, arbitrary())(s)
        }
    );
    assert forall |object: DynamicObjectView| spec.entails(#[trigger] pre_with_object(object).leads_to(lift_state(current_state_matches(rabbitmq))))
    by {
        let p1 = lift_state(|s: ClusterState| {
            &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
            &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, arbitrary())(s)
        });
        let p2 = lift_state(|s: ClusterState| {
            &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
            &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
            &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, object)(s)
        });

        assert_by(
            spec.entails(p1.leads_to(p2)),
            {
                let pre_and_req_in_flight = |req_msg| lift_state(
                    |s: ClusterState| {
                        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                        &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, req_msg, arbitrary())(s)
                    }
                );
                let pre_and_exists_resp_in_flight = lift_state(
                    |s: ClusterState| {
                        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                        &&& at_after_get_server_config_map_step_with_rabbitmq_and_exists_ok_resp_in_flight(rabbitmq, object)(s)
                    }
                );
                let pre_and_resp_in_flight = |resp_msg| lift_state(
                    |s: ClusterState| {
                        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                        &&& resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, resp_msg, arbitrary())(s)
                        &&& resp_msg.content.get_get_response().res.is_Ok()
                        &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
                    }
                );

                assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight))
                by {
                    lemma_receives_ok_resp_at_after_get_server_config_map_step_with_rabbitmq(spec, rabbitmq, rest_id, req_msg, object);
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
                    lemma_from_after_get_server_config_map_step_to_after_update_server_config_map_step(spec, rabbitmq, rest_id, resp_msg, object);
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

        assert_by(
            spec.entails(p2.leads_to(lift_state(current_state_matches(rabbitmq)))),
            {
                let pre_and_req_in_flight = |req_msg| lift_state(
                    |s: ClusterState| {
                        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                        &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, req_msg, object)(s)
                    }
                );
                assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(lift_state(current_state_matches(rabbitmq))))
                by {
                    lemma_cm_is_updated_at_after_update_server_config_map_step_with_rabbitmq(spec, rabbitmq, rest_id, req_msg, object);
                }
                leads_to_exists_intro(spec, pre_and_req_in_flight, lift_state(current_state_matches(rabbitmq)));
                assert_by(
                    tla_exists(pre_and_req_in_flight) == p2,
                    {
                        assert forall |ex| #[trigger] p2.satisfied_by(ex)
                        implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                            let req_msg = ex.head().pending_req_of(rabbitmq.object_ref());
                            assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
                        }
                        temp_pred_equality(tla_exists(pre_and_req_in_flight), p2);
                    }
                );
            }
        );

        leads_to_trans_temp(spec, p1, p2, lift_state(current_state_matches(rabbitmq)));
    }
    leads_to_exists_intro(spec, pre_with_object, lift_state(current_state_matches(rabbitmq)));
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
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, rest_id: nat, req_msg: Message, object: DynamicObjectView
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(safety::at_most_one_update_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))),
        spec.entails(always(lift_state(safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                    &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                    &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, req_msg, arbitrary())(s)
                }
            )
                .leads_to(lift_state(
                    |s: ClusterState| {
                        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                        &&& at_after_get_server_config_map_step_with_rabbitmq_and_exists_ok_resp_in_flight(rabbitmq, object)(s)
                    }
                ))
        ),
{
    let pre = |s: ClusterState| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
        &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, req_msg, arbitrary())(s)
    };
    let post = |s: ClusterState| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
        &&& at_after_get_server_config_map_step_with_rabbitmq_and_exists_ok_resp_in_flight(rabbitmq, object)(s)
    };
    let input = Option::Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& safety::at_most_one_update_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)(s)
        &&& safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(safety::at_most_one_update_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)),
        lift_state(safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
        .and(lift_state(RMQCluster::busy_disabled()))
        .and(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))
        .and(lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(safety::at_most_one_update_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))
        .and(lift_state(safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = handle_get_request(req_msg, s.kubernetes_api_state).1;
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
        let resp_msg = handle_get_request(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
        });
    }

    RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, handle_request(), pre, post
    );
}

proof fn lemma_cm_is_updated_at_after_update_server_config_map_step_with_rabbitmq(
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, rest_id: nat, req_msg: Message, object: DynamicObjectView
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(safety::at_most_one_update_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))),
        spec.entails(always(lift_state(safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                    &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                    &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, req_msg, object)(s)
                }
            )
                .leads_to(lift_state(
                    |s: ClusterState| {
                        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).is_Ok()
                        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).get_Ok_0().data == make_server_config_map(rabbitmq).data
                    }
                ))
        ),
{
    let pre = |s: ClusterState| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
        &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, req_msg, object)(s)
    };
    let post = |s: ClusterState| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).is_Ok()
        &&& ConfigMapView::from_dynamic_object(s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref()))).get_Ok_0().data == make_server_config_map(rabbitmq).data
    };
    let input = Option::Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& safety::at_most_one_update_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)(s)
        &&& safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(safety::at_most_one_update_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)),
        lift_state(safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
        .and(lift_state(RMQCluster::busy_disabled()))
        .and(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))
        .and(lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))
        .and(lift_state(safety::at_most_one_update_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))
        .and(lift_state(safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))
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
        spec, input, stronger_next, handle_request(), pre, post
    );
}

proof fn lemma_from_after_get_server_config_map_step_to_after_update_server_config_map_step(
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, rest_id: nat, resp_msg: Message, object: DynamicObjectView
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(safety::at_most_one_update_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))),
        spec.entails(always(lift_state(safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: ClusterState| {
                &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                &&& resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, resp_msg, arbitrary())(s)
                &&& resp_msg.content.get_get_response().res.is_Ok()
                &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
            })
                .leads_to(lift_state(|s: ClusterState| {
                    &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
                    &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
                    &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, object)(s)
                }))
        ),
{
    let pre = |s: ClusterState| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
        &&& resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, resp_msg, arbitrary())(s)
        &&& resp_msg.content.get_get_response().res.is_Ok()
        &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
    };
    let post = |s: ClusterState| {
        &&& s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        &&& s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())) == object
        &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, object)(s)
    };
    let input = (Option::Some(resp_msg), Option::None, Option::Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())(s)
        &&& RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())(s)
        &&& RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& safety::at_most_one_update_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)(s)
        &&& safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)(s)
    };

    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())),
        lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(safety::at_most_one_update_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)),
        lift_state(safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::crash_disabled()))
        .and(lift_state(RMQCluster::busy_disabled()))
        .and(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))
        .and(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))
        .and(lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))
        .and(lift_state(safety::at_most_one_update_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))
        .and(lift_state(safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))
    );

    RMQCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next,
        RMQCluster::continue_reconcile(), pre, post
    );
}

proof fn lemma_server_config_map_is_stable(
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, rest_id: nat, p: TempPred<ClusterState>
)
    requires
        spec.entails(p.leads_to(lift_state(current_state_matches(rabbitmq)))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))),
        spec.entails(always(lift_state(safety::every_update_cm_req_since_rest_id_does_the_same(rabbitmq, rest_id)))),
    ensures
        spec.entails(p.leads_to(always(lift_state(current_state_matches(rabbitmq))))),
{
    let post = current_state_matches(rabbitmq);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)(s)
        &&& safety::every_update_cm_req_since_rest_id_does_the_same(rabbitmq, rest_id)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)),
        lift_state(safety::every_update_cm_req_since_rest_id_does_the_same(rabbitmq, rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(safety::no_delete_cm_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)))
        .and(lift_state(safety::every_update_cm_req_since_rest_id_does_the_same(rabbitmq, rest_id)))
    );

    assert forall |s, s_prime| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        ConfigMapView::spec_integrity_is_preserved_by_marshal();
    }

    leads_to_stable_temp(spec, lift_action(stronger_next), p, lift_state(post));
}

}
