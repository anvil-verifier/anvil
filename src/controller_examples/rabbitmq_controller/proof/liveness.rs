// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::{
    proof::{
        cluster, cluster_safety, controller_runtime, controller_runtime_eventual_safety,
        controller_runtime_liveness, controller_runtime_safety, kubernetes_api_liveness,
        kubernetes_api_safety,
    },
    spec::{
        cluster::*,
        controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
        controller::controller_runtime::{
            continue_reconcile, end_reconcile, run_scheduled_reconcile,
        },
        controller::state_machine::controller,
        kubernetes_api::state_machine::{
            handle_create_request, handle_get_request, handle_request, transition_by_etcd,
            update_is_noop,
        },
        message::*,
    },
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
        &&& s.resource_key_exists(make_stateful_set_key(rabbitmq.object_ref()))
        &&& StatefulSetView::from_dynamic_object(s.resource_obj_of(make_stateful_set_key(rabbitmq.object_ref()))).is_Ok()
        &&& StatefulSetView::from_dynamic_object(s.resource_obj_of(make_stateful_set_key(rabbitmq.object_ref()))).get_Ok_0().spec == make_stateful_set(rabbitmq).spec
    }
}

// The liveness property says []cluster::desired_state_is(rabbitmq) ~> []current_state_matches(rabbitmq).
spec fn liveness(rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState>
    recommends
        rabbitmq.well_formed(),
{
    always(lift_state(cluster::desired_state_is(rabbitmq))).leads_to(always(lift_state(current_state_matches(rabbitmq))))
}

// We prove init /\ []next /\ []wf |= []cluster::desired_state_is(rabbitmq) ~> []current_state_matches(rabbitmq) holds for each rabbitmq.
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
    always(lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()))
    .and(tla_forall(|input| kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| controller_next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>().weak_fairness(input)))
    .and(tla_forall(|input| schedule_controller_reconcile().weak_fairness(input)))
    .and(disable_crash().weak_fairness(()))
    .and(disable_busy().weak_fairness(()))
}

proof fn next_with_wf_is_stable()
    ensures
        valid(stable(next_with_wf())),
{
    always_p_is_stable(lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()));
    cluster::tla_forall_action_weak_fairness_is_stable(kubernetes_api_next::<RabbitmqClusterView, RabbitmqReconcileState>());
    cluster::tla_forall_action_weak_fairness_is_stable(controller_next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>());
    cluster::tla_forall_action_weak_fairness_is_stable(schedule_controller_reconcile::<RabbitmqClusterView, RabbitmqReconcileState>());
    cluster::action_weak_fairness_is_stable(disable_crash::<RabbitmqClusterView, RabbitmqReconcileState>());
    cluster::action_weak_fairness_is_stable(disable_busy::<RabbitmqClusterView, RabbitmqReconcileState>());
    stable_and_n!(
        always(lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>())),
        tla_forall(|input| kubernetes_api_next::<RabbitmqClusterView, RabbitmqReconcileState>().weak_fairness(input)),
        tla_forall(|input| controller_next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>().weak_fairness(input)),
        tla_forall(|input| schedule_controller_reconcile().weak_fairness(input)),
        disable_crash().weak_fairness(()),
        disable_busy().weak_fairness(())
    );
}

// All assumptions that makes liveness possible, such as controller crash no longer happens,
// the cr's spec always remains unchanged, and so on.
spec fn assumptions(rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    always(lift_state(crash_disabled()))
    .and(always(lift_state(busy_disabled())))
    .and(always(lift_state(cluster::desired_state_is(rabbitmq))))
    .and(always(lift_state(controller_runtime_eventual_safety::the_object_in_schedule_has_spec_as(rabbitmq))))
    .and(always(lift_state(controller_runtime_eventual_safety::the_object_in_reconcile_has_spec_as(rabbitmq))))
}

proof fn assumptions_is_stable(rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(assumptions(rabbitmq))),
{
    stable_and_always_n!(
        lift_state(crash_disabled::<RabbitmqClusterView, RabbitmqReconcileState>()),
        lift_state(busy_disabled::<RabbitmqClusterView, RabbitmqReconcileState>()),
        lift_state(cluster::desired_state_is::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq)),
        lift_state(controller_runtime_eventual_safety::the_object_in_schedule_has_spec_as::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq)),
        lift_state(controller_runtime_eventual_safety::the_object_in_reconcile_has_spec_as::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq))
    );
}

// The safety invariants that are required to prove liveness.
spec fn invariants(rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref()))))
    .and(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref()))))
    .and(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(cluster_safety::each_object_in_etcd_is_well_formed())))
    .and(always(lift_state(cluster_safety::each_scheduled_key_is_consistent_with_its_object())))
    .and(always(lift_state(cluster_safety::each_key_in_reconcile_is_consistent_with_its_object())))
    .and(always(lift_state(safety::pending_msg_at_after_create_stateful_set_step_is_create_sts_req(rabbitmq.object_ref()))))
    .and(always(lift_state(safety::pending_msg_at_after_update_stateful_set_step_is_update_sts_req(rabbitmq.object_ref()))))
    .and(always(lift_state(controller_runtime::no_pending_req_at_reconcile_init_state::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>(rabbitmq.object_ref()))))
    .and(always(lift_state(controller_runtime::pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq.object_ref(), rabbitmq_reconcile_state(RabbitmqReconcileStep::AfterCreateHeadlessService)))))
    .and(always(lift_state(controller_runtime::pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq.object_ref(), rabbitmq_reconcile_state(RabbitmqReconcileStep::AfterCreateService)))))
    .and(always(lift_state(controller_runtime::pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq.object_ref(), rabbitmq_reconcile_state(RabbitmqReconcileStep::AfterCreateErlangCookieSecret)))))
    .and(always(lift_state(controller_runtime::pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq.object_ref(), rabbitmq_reconcile_state(RabbitmqReconcileStep::AfterCreateDefaultUserSecret)))))
    .and(always(lift_state(controller_runtime::pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq.object_ref(), rabbitmq_reconcile_state(RabbitmqReconcileStep::AfterCreatePluginsConfigMap)))))
    .and(always(lift_state(controller_runtime::pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq.object_ref(), rabbitmq_reconcile_state(RabbitmqReconcileStep::AfterGetServerConfigMap)))))
    .and(always(lift_state(controller_runtime::pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq.object_ref(), rabbitmq_reconcile_state(RabbitmqReconcileStep::AfterCreateServerConfigMap)))))
    .and(always(lift_state(controller_runtime::pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq.object_ref(), rabbitmq_reconcile_state(RabbitmqReconcileStep::AfterUpdateServerConfigMap)))))
    .and(always(lift_state(controller_runtime::pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq.object_ref(), rabbitmq_reconcile_state(RabbitmqReconcileStep::AfterCreateServiceAccount)))))
    .and(always(lift_state(controller_runtime::pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq.object_ref(), rabbitmq_reconcile_state(RabbitmqReconcileStep::AfterCreateRole)))))
    .and(always(lift_state(controller_runtime::pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq.object_ref(), rabbitmq_reconcile_state(RabbitmqReconcileStep::AfterCreateRoleBinding)))))
    .and(always(lift_state(controller_runtime::pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq.object_ref(), rabbitmq_reconcile_state(RabbitmqReconcileStep::AfterGetStatefulSet)))))
    .and(always(lift_state(controller_runtime::pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq.object_ref(), rabbitmq_reconcile_state(RabbitmqReconcileStep::AfterCreateStatefulSet)))))
    .and(always(lift_state(controller_runtime::pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<RabbitmqClusterView, RabbitmqReconcileState>(rabbitmq.object_ref(), rabbitmq_reconcile_state(RabbitmqReconcileStep::AfterUpdateStatefulSet)))))
}

#[verifier(external_body)]
proof fn invariants_is_stable(rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(invariants(rabbitmq))),
{}

// Some other invariants requires to prove liveness.
// Note that different from the above invariants, these do not hold for the entire execution from init.
// They only hold since some point (e.g., when the rest id counter is the same as rest_id).
// Some of these invariants are also based on the assumptions.
spec fn invariants_since_rest_id(rabbitmq: RabbitmqClusterView, rest_id: RestId) -> TempPred<ClusterState> {
    always(lift_state(rest_id_counter_is_no_smaller_than(rest_id)))
    .and(always(lift_state(safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))))
    .and(always(lift_state(safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))))
    .and(always(lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))))
    .and(always(lift_state(safety::every_update_sts_req_since_rest_id_does_the_same(rabbitmq, rest_id))))
}

proof fn invariants_since_rest_id_is_stable(rabbitmq: RabbitmqClusterView, rest_id: RestId)
    ensures
        valid(stable(invariants_since_rest_id(rabbitmq, rest_id))),
{
    stable_and_always_n!(
        lift_state(rest_id_counter_is_no_smaller_than::<RabbitmqClusterView, RabbitmqReconcileState>(rest_id)),
        lift_state(safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)),
        lift_state(safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)),
        lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id)),
        lift_state(safety::every_update_sts_req_since_rest_id_does_the_same(rabbitmq, rest_id))
    );
}

// This invariant is also used to prove liveness.
// Different from above, it only holds after some time since the rest id counter is the same as rest_id.
spec fn invariants_led_to_by_rest_id(rabbitmq: RabbitmqClusterView, rest_id: RestId) -> TempPred<ClusterState> {
    always(lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)))
}

#[verifier(external_body)]
proof fn liveness_proof(rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
    ensures
        cluster_spec().entails(liveness(rabbitmq)),
{}

proof fn lemma_true_leads_to_always_current_state_matches_rabbitmq_from_idle_with_rest_id(rabbitmq: RabbitmqClusterView, rest_id: RestId)
    requires
        rabbitmq.well_formed(),
    ensures
        lift_state(rest_id_counter_is(rest_id))
        .and(next_with_wf()).and(invariants(rabbitmq)).and(assumptions(rabbitmq))
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(rabbitmq))))
        ),
{
    let spec = next_with_wf().and(invariants(rabbitmq)).and(assumptions(rabbitmq));
    let spec_with_rest_id = lift_state(rest_id_counter_is(rest_id))
                            .and(next_with_wf()).and(invariants(rabbitmq)).and(assumptions(rabbitmq));
    // To prove the liveness, we need some extra invariants (invariants_since_rest_id and invariants_led_to_by_rest_id)
    // that only holds since the rest id counter is rest_id.
    assert_by(
        spec_with_rest_id.and(invariants_since_rest_id(rabbitmq, rest_id)).entails(
            invariants_led_to_by_rest_id(rabbitmq, rest_id).leads_to(always(lift_state(current_state_matches(rabbitmq))))
        ),
        {
            lemma_true_leads_to_always_current_state_matches_rabbitmq_under_eventual_invariants(rabbitmq, rest_id);
            assert_by(
                valid(stable(spec.and(invariants_since_rest_id(rabbitmq, rest_id)))),
                {
                    next_with_wf_is_stable();
                    invariants_is_stable(rabbitmq);
                    assumptions_is_stable(rabbitmq);
                    invariants_since_rest_id_is_stable(rabbitmq, rest_id);

                    stable_and_n!(next_with_wf(), invariants(rabbitmq), assumptions(rabbitmq), invariants_since_rest_id(rabbitmq, rest_id));
                }
            );
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

    kubernetes_api_liveness::lemma_true_leads_to_always_no_req_before_rest_id_is_in_flight::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>(
        spec_with_rest_id.and(invariants_since_rest_id(rabbitmq, rest_id)), rest_id
    );

    // Here we eliminate invariants_led_to_by_rest_id using leads_to_trans_temp
    leads_to_trans_temp(spec_with_rest_id.and(invariants_since_rest_id(rabbitmq, rest_id)), true_pred(), invariants_led_to_by_rest_id(rabbitmq, rest_id), always(lift_state(current_state_matches(rabbitmq))));

    assert_by(
        spec_with_rest_id.entails(invariants_since_rest_id(rabbitmq, rest_id)),
        {
            eliminate_always(spec_with_rest_id, lift_state(controller_runtime_safety::every_in_flight_msg_has_lower_id_than_allocator()));
            eliminate_always(spec_with_rest_id, lift_state(safety::pending_msg_at_after_create_stateful_set_step_is_create_sts_req(rabbitmq.object_ref())));
            eliminate_always(spec_with_rest_id, lift_state(safety::pending_msg_at_after_update_stateful_set_step_is_update_sts_req(rabbitmq.object_ref())));

            cluster_safety::lemma_always_rest_id_counter_is_no_smaller_than::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>(spec_with_rest_id, rest_id);
            safety::lemma_always_at_most_one_create_sts_req_since_rest_id_is_in_flight(spec_with_rest_id, rabbitmq.object_ref(), rest_id);
            safety::lemma_always_at_most_one_update_sts_req_since_rest_id_is_in_flight(spec_with_rest_id, rabbitmq.object_ref(), rest_id);
            safety::lemma_always_no_delete_sts_req_since_rest_id_is_in_flight(spec_with_rest_id, rabbitmq.object_ref(), rest_id);
            safety::lemma_always_every_update_sts_req_since_rest_id_does_the_same(spec_with_rest_id, rabbitmq, rest_id);

            entails_and_n!(
                spec_with_rest_id,
                always(lift_state(rest_id_counter_is_no_smaller_than(rest_id))),
                always(lift_state(safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))),
                always(lift_state(safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))),
                always(lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))),
                always(lift_state(safety::every_update_sts_req_since_rest_id_does_the_same(rabbitmq, rest_id)))
            );
        }
    );

    // And we eliminate invariants_since_rest_id using simplify_predicate.
    simplify_predicate(spec_with_rest_id, invariants_since_rest_id(rabbitmq, rest_id));
}

// This lemma proves that with all the invariants, assumptions, and even invariants that only hold since rest id counter is rest_id,
// true ~> []current_state_matches(rabbitmq).
#[verifier(external_body)]
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
}

proof fn lemma_from_reconcile_idle_to_scheduled(spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()))),
        spec.entails(tla_forall(|i| schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(cluster::desired_state_is(rabbitmq)))),
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

    controller_runtime_liveness::lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec(
        spec, input, next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>(), cluster::desired_state_is(rabbitmq), pre, post
    );
    valid_implies_implies_leads_to(spec, lift_state(post), lift_state(post));
    or_leads_to_combine(spec, pre, post, post);
    temp_pred_equality(lift_state(pre).or(lift_state(post)), lift_state(|s: ClusterState| {!s.reconcile_state_contains(rabbitmq.object_ref())}));
}

proof fn lemma_from_scheduled_to_init_step(spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()))),
        spec.entails(tla_forall(|i| controller_next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(cluster_safety::each_scheduled_key_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(controller_runtime_eventual_safety::the_object_in_schedule_has_spec_as(rabbitmq)))),
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
    let input = (Option::None, Option::Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& cluster_safety::each_scheduled_key_is_consistent_with_its_object()(s)
        &&& controller_runtime_eventual_safety::the_object_in_schedule_has_spec_as(rabbitmq)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()),
        lift_state(crash_disabled()),
        lift_state(cluster_safety::each_scheduled_key_is_consistent_with_its_object()),
        lift_state(controller_runtime_eventual_safety::the_object_in_schedule_has_spec_as(rabbitmq))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(cluster_safety::each_scheduled_key_is_consistent_with_its_object()))
        .and(lift_state(controller_runtime_eventual_safety::the_object_in_schedule_has_spec_as(rabbitmq)))
    );

    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>(
        spec, input, stronger_next,
        run_scheduled_reconcile::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>(), pre, post
    );
}

proof fn lemma_from_init_step_to_after_create_headless_service_step(
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(always(lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()))),
        spec.entails(tla_forall(|i| controller_next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init))
                .leads_to(lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateHeadlessService, rabbitmq, arbitrary())))
        ),
{
    let pre = no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init);
    let post = pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateHeadlessService, rabbitmq, arbitrary());
    let input = (Option::None, Option::Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()),
        lift_state(crash_disabled())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>())
        .and(lift_state(crash_disabled()))
    );

    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>(
        spec, input, stronger_next,
        continue_reconcile::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>(), pre, post
    );
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
        spec.entails(always(lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()))),
        spec.entails(tla_forall(|i| controller_next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>().weak_fairness(i))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(busy_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        step != RabbitmqReconcileStep::Error, step != RabbitmqReconcileStep::Done,
        // next_step != RabbitmqReconcileStep::Init,
        forall |rabbitmq_1: RabbitmqClusterView, resp_o: Option<APIResponse>|
            #[trigger] reconcile_core(rabbitmq_1, resp_o, RabbitmqReconcileState{ reconcile_step: step }).0.reconcile_step == next_step
            && reconcile_core(rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).1.is_Some()
            && (rabbitmq_1.object_ref() == rabbitmq.object_ref() && rabbitmq_1.spec == rabbitmq.spec ==>
            forall |object: DynamicObjectView| #[trigger] is_correct_pending_request_at_rabbitmq_step(
                next_step, reconcile_core(rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).1.get_Some_0(), rabbitmq, object
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
        spec.entails(always(lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(busy_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
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
        &&& next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& busy_disabled()(s)
        &&& controller_runtime_safety::every_in_flight_msg_has_unique_id()(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()),
        lift_state(crash_disabled()),
        lift_state(busy_disabled()),
        lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(busy_disabled()))
        .and(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = transition_by_etcd(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        });
    }

    kubernetes_api_liveness::lemma_pre_leads_to_post_by_kubernetes_api::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>(
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
        spec.entails(always(lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()))),
        spec.entails(tla_forall(|i| controller_next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(busy_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        step != RabbitmqReconcileStep::Done, step != RabbitmqReconcileStep::Error,
        // result_step != RabbitmqReconcileStep::Init,
        // This forall rabbitmq_1 constraint is used because the cr passed to reconcile_core is not necessarily rabbitmq here.
        // We only know that rabbitmq_1.object_ref() == rabbitmq.object_ref() && rabbitmq_1.spec == rabbitmq.spec.
        forall |rabbitmq_1: RabbitmqClusterView, resp_o: Option<APIResponse>|
            #[trigger] reconcile_core(rabbitmq_1, resp_o, RabbitmqReconcileState{ reconcile_step: step }).0.reconcile_step == result_step
            && reconcile_core(rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).1.is_Some()
            && (rabbitmq_1.object_ref() == rabbitmq.object_ref() && rabbitmq_1.spec == rabbitmq.spec ==>
            forall |object: DynamicObjectView| #[trigger] is_correct_pending_request_at_rabbitmq_step(
                result_step, reconcile_core(rabbitmq, resp_o, RabbitmqReconcileState{ reconcile_step: step }).1.get_Some_0(), rabbitmq, object
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
    let input = (Option::Some(resp_msg), Option::Some(rabbitmq.object_ref()));

    // For every part of stronger_next:
    //   - next(): the next predicate of the state machine
    //   - crash_disabled(): to ensure that the reconcile process can continue
    //   - busy_disabled(): to ensure that the request will get its expected response
    //    (Note that this is not required for termination)
    //   - each_resp_matches_at_most_one_pending_req: to make sure that the resp_msg will not be used by other cr
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& busy_disabled()(s)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())(s)
    };

    entails_always_and_n!(
        spec,
        lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()),
        lift_state(crash_disabled()),
        lift_state(busy_disabled()),
        lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(busy_disabled()))
        .and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| next_step::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>(s, s_prime, step);
        match step {
            Step::ControllerStep(input) => {
                if input.1.is_Some() && input.1.get_Some_0() == rabbitmq.object_ref() {
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

    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>(
        spec, input, stronger_next,
        continue_reconcile::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>(), pre, post
    );
}

}
