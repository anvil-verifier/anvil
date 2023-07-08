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
        spec.and(invariants_since_rest_id(rabbitmq, rest_id)), rest_id
    );

    // Here we eliminate invariants_led_to_by_rest_id using leads_to_trans_temp
    leads_to_trans_temp(spec.and(invariants_since_rest_id(rabbitmq, rest_id)), true_pred(), invariants_led_to_by_rest_id(rabbitmq, rest_id), always(lift_state(current_state_matches(rabbitmq))));

    assert_by(
        spec.entails(invariants_since_rest_id(rabbitmq, rest_id)),
        {
            eliminate_always(spec, lift_state(controller_runtime_safety::every_in_flight_msg_has_lower_id_than_allocator()));
            eliminate_always(spec, lift_state(safety::pending_msg_at_after_create_stateful_set_step_is_create_sts_req(rabbitmq.object_ref())));
            eliminate_always(spec, lift_state(safety::pending_msg_at_after_update_stateful_set_step_is_update_sts_req(rabbitmq.object_ref())));

            cluster_safety::lemma_always_rest_id_counter_is_no_smaller_than::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>(spec, rest_id);
            safety::lemma_always_at_most_one_create_sts_req_since_rest_id_is_in_flight(spec, rabbitmq.object_ref(), rest_id);
            safety::lemma_always_at_most_one_update_sts_req_since_rest_id_is_in_flight(spec, rabbitmq.object_ref(), rest_id);
            safety::lemma_always_no_delete_sts_req_since_rest_id_is_in_flight(spec, rabbitmq.object_ref(), rest_id);
            safety::lemma_always_every_update_sts_req_since_rest_id_does_the_same(spec, rabbitmq, rest_id);

            entails_and_n!(
                spec,
                always(lift_state(rest_id_counter_is_no_smaller_than(rest_id))),
                always(lift_state(safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))),
                always(lift_state(safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))),
                always(lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(rabbitmq.object_ref(), rest_id))),
                always(lift_state(safety::every_update_sts_req_since_rest_id_does_the_same(rabbitmq, rest_id)))
            );
        }
    );

    // And we eliminate invariants_since_rest_id using simplify_predicate.
    simplify_predicate(spec, invariants_since_rest_id(rabbitmq, rest_id));
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
{}

}
