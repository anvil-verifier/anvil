// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
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
    proof::{
        helper_invariants,
        liveness::{
            property::*,
            resource_match::*,
            spec::*,
            stateful_set_match::{
                lemma_from_after_get_stateful_set_step_to_stateful_set_matches,
                lemma_stateful_set_is_stable,
            },
            terminate,
        },
        predicate::*,
        resource::*,
    },
    spec::{reconciler::*, resource::*, types::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{map_lib::*, string_view::*};
use vstd::{prelude::*, string::*};

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
    assumption_and_invariants_of_all_phases_is_stable(rabbitmq);
    lemma_true_leads_to_always_current_state_matches(rabbitmq);
    reveal_with_fuel(spec_before_phase_n, 8);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(7, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(6, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(5, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(4, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(3, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(2, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(1, rabbitmq);

    let assumption = always(lift_state(RMQCluster::desired_state_is(rabbitmq)));
    unpack_conditions_from_spec(invariants(rabbitmq), assumption, true_pred(), always(lift_state(current_state_matches(rabbitmq))));
    temp_pred_equality(true_pred().and(assumption), assumption);

    entails_trans(
        cluster_spec().and(derived_invariants_since_beginning(rabbitmq)), invariants(rabbitmq),
        always(lift_state(RMQCluster::desired_state_is(rabbitmq))).leads_to(always(lift_state(current_state_matches(rabbitmq))))
    );
    sm_spec_entails_all_invariants(rabbitmq);
    simplify_predicate(cluster_spec(), derived_invariants_since_beginning(rabbitmq));
}

proof fn spec_before_phase_n_entails_true_leads_to_current_state_matches(i: nat, rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
        1 <= i <= 7,
        valid(stable(spec_before_phase_n(i, rabbitmq))),
        spec_before_phase_n(i + 1, rabbitmq).entails(true_pred().leads_to(always(lift_state(current_state_matches(rabbitmq)))))
    ensures
        spec_before_phase_n(i, rabbitmq).entails(true_pred().leads_to(always(lift_state(current_state_matches(rabbitmq))))),
{
    reveal_with_fuel(spec_before_phase_n, 8);
    temp_pred_equality(spec_before_phase_n(i + 1, rabbitmq), spec_before_phase_n(i, rabbitmq).and(invariants_since_phase_n(i, rabbitmq)));
    spec_of_previous_phases_entails_eventually_new_invariants(i, rabbitmq);
    unpack_conditions_from_spec(spec_before_phase_n(i, rabbitmq), invariants_since_phase_n(i, rabbitmq), true_pred(), always(lift_state(current_state_matches(rabbitmq))));
    temp_pred_equality(true_pred().and(invariants_since_phase_n(i, rabbitmq)), invariants_since_phase_n(i, rabbitmq));
    leads_to_trans_temp(spec_before_phase_n(i, rabbitmq), true_pred(), invariants_since_phase_n(i, rabbitmq), always(lift_state(current_state_matches(rabbitmq))));
}

proof fn lemma_true_leads_to_always_current_state_matches(rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
    ensures
        assumption_and_invariants_of_all_phases(rabbitmq)
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(rabbitmq))))
        ),
{
    let spec = assumption_and_invariants_of_all_phases(rabbitmq);
    // lemma_true_leads_to_state_matches_for_all_resources(rabbitmq);
    // assert forall |sub_resource: SubResource| sub_resource != SubResource::StatefulSet implies spec.entails(
    //     true_pred().leads_to(always(lift_state(#[trigger] sub_resource_state_matches(sub_resource, rabbitmq))))
    // ) by {
    //     always_tla_forall_apply_for_sub_resource(spec, sub_resource, rabbitmq);
    //     lemma_resource_object_is_stable(spec, sub_resource, rabbitmq, true_pred());
    // }
    // lemma_true_leads_to_always_stateful_set_matches(rabbitmq);
    lemma_true_leads_to_always_state_matches_for_all_resources(rabbitmq);
    let a_to_p = |res: SubResource| lift_state(sub_resource_state_matches(res, rabbitmq));
    helper_invariants::leads_to_always_tla_forall_subresource(spec, true_pred(), a_to_p);
    assert forall |ex| #[trigger] tla_forall(a_to_p).satisfied_by(ex) implies lift_state(current_state_matches(rabbitmq)).satisfied_by(ex) by {
        let s = ex.head();
        assert forall |res: SubResource| #[trigger] resource_state_matches(res, rabbitmq, s.resources()) by {
            tla_forall_apply(a_to_p, res);
            assert(a_to_p(res).satisfied_by(ex));
            assert(sub_resource_state_matches(res, rabbitmq)(s));
        }
    }
    temp_pred_equality(tla_forall(|res: SubResource| lift_state(sub_resource_state_matches(res, rabbitmq))), lift_state(current_state_matches(rabbitmq)));
}

proof fn lemma_true_leads_to_always_state_matches_for_all_resources(rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
    ensures
        forall |sub_resource: SubResource|
            assumption_and_invariants_of_all_phases(rabbitmq)
            .entails(
                true_pred().leads_to(always(lift_state(#[trigger] sub_resource_state_matches(sub_resource, rabbitmq))))
            ),
{
    let spec = assumption_and_invariants_of_all_phases(rabbitmq);
    lemma_true_leads_to_state_matches_for_all_resources(rabbitmq);
    assert forall |sub_resource: SubResource| sub_resource != SubResource::StatefulSet implies
    spec.entails(
        true_pred().leads_to(always(lift_state(#[trigger] sub_resource_state_matches(sub_resource, rabbitmq))))
    ) by {
        always_tla_forall_apply_for_sub_resource(spec, sub_resource, rabbitmq);
        lemma_resource_object_is_stable(spec, sub_resource, rabbitmq, true_pred());
    }
    lemma_true_leads_to_always_stateful_set_matches(rabbitmq);
}

proof fn lemma_true_leads_to_state_matches_for_all_resources(rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
    ensures
        forall |sub_resource: SubResource|
            assumption_and_invariants_of_all_phases(rabbitmq)
            .entails(
                true_pred().leads_to(lift_state(#[trigger] sub_resource_state_matches(sub_resource, rabbitmq)))
            ),
{
    let spec = assumption_and_invariants_of_all_phases(rabbitmq);

    assert forall |action: ActionKind, sub_resource: SubResource| #![auto] spec.entails(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(action, sub_resource)))))) by {
        always_tla_forall_apply(spec, |step: (ActionKind, SubResource)| lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.0, step.1)))), (action, sub_resource));
    }

    // The use of termination property ensures spec |= true ~> reconcile_idle.
    terminate::reconcile_eventually_terminates(spec, rabbitmq);
    // Then we can continue to show that spec |= reconcile_idle ~> []current_state_matches(rabbitmq).

    // The following two lemmas show that spec |= reconcile_idle ~> init /\ no_pending_req.
    lemma_from_reconcile_idle_to_scheduled(spec, rabbitmq);
    lemma_from_scheduled_to_init_step(spec, rabbitmq);

    // After applying this lemma, we get spec |= init /\ no_pending_req ~> create_headless_service /\ pending_req.
    lemma_from_init_step_to_after_create_headless_service_step(spec, rabbitmq);

    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(res, rabbitmq)), SubResource::ServerConfigMap);
    // We first show that the reconciler can go to at_after_get_resource_step(next_resource) from at_after_get_resource_step(sub_resource)
    // where sub_resource cannot be StatefulSet because it's the last resource to be processed and doesn't have its next_resource.
    // Through this, we can string all the resources together in sequence. This also means that the system can go to any
    // at_after_get_resource_step(sub_resource) from an arbitrary state.
    assert forall |sub_resource: SubResource| sub_resource != SubResource::StatefulSet implies
    spec.entails(
        lift_state(#[trigger] pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq))
            .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource_get_step_and_request(rabbitmq, sub_resource).0.get_AfterKRequestStep_1(), rabbitmq)))
    ) by {
        always_tla_forall_apply_for_sub_resource(spec, sub_resource, rabbitmq);
        let next_resource = next_resource_get_step_and_request(rabbitmq, sub_resource).0.get_AfterKRequestStep_1();
        lemma_from_after_get_resource_step_to_resource_matches(spec, rabbitmq, sub_resource, next_resource);
    }
    // Thanks to the recursive construction of macro.
    leads_to_trans_n!(
        spec, true_pred(), lift_state(|s: RMQCluster| { !s.ongoing_reconciles().contains_key(rabbitmq.object_ref()) }),
        lift_state(|s: RMQCluster| { !s.ongoing_reconciles().contains_key(rabbitmq.object_ref()) && s.scheduled_reconciles().contains_key(rabbitmq.object_ref())}),
        lift_state(no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::HeadlessService, rabbitmq)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::Service, rabbitmq)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ErlangCookieSecret, rabbitmq)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::DefaultUserSecret, rabbitmq)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::PluginsConfigMap, rabbitmq)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, rabbitmq)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::Role, rabbitmq)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::RoleBinding, rabbitmq)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, rabbitmq))
    );

    // Since we already have true ~> at_after_get_resource_step(sub_resource), and we can get at_after_get_resource_step(sub_resource)
    // ~> sub_resource_state_matches(sub_resource, rabbitmq) by applying lemma lemma_from_after_get_resource_step_to_resource_matches,
    // we now have true ~> sub_resource_state_matches(sub_resource, rabbitmq).
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(lift_state(#[trigger] sub_resource_state_matches(sub_resource, rabbitmq)))) by {
        always_tla_forall_apply_for_sub_resource(spec, sub_resource, rabbitmq);
        if sub_resource != SubResource::StatefulSet {
            let next_resource = next_resource_get_step_and_request(rabbitmq, sub_resource).0.get_AfterKRequestStep_1();
            lemma_from_after_get_resource_step_to_resource_matches(spec, rabbitmq, sub_resource, next_resource);
            leads_to_trans_temp(
                spec, true_pred(), lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq)),
                lift_state(sub_resource_state_matches(sub_resource, rabbitmq))
            );
        } else {
            lemma_from_after_get_stateful_set_step_to_stateful_set_matches(spec, rabbitmq);
            leads_to_trans_temp(
                spec, true_pred(), lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, rabbitmq)),
                lift_state(sub_resource_state_matches(SubResource::StatefulSet, rabbitmq))
            );
        }
    }
}

proof fn lemma_true_leads_to_always_stateful_set_matches(rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
        assumption_and_invariants_of_all_phases(rabbitmq)
        .entails(
            true_pred().leads_to(always(lift_state(sub_resource_state_matches(SubResource::ServerConfigMap, rabbitmq))))
        ),
        assumption_and_invariants_of_all_phases(rabbitmq)
        .entails(
            true_pred().leads_to(lift_state(sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)))
        )
    ensures
        assumption_and_invariants_of_all_phases(rabbitmq)
        .entails(
            true_pred().leads_to(always(lift_state(sub_resource_state_matches(SubResource::StatefulSet, rabbitmq))))
        ),
{
    let spec = assumption_and_invariants_of_all_phases(rabbitmq).and(always(lift_state(sub_resource_state_matches(SubResource::ServerConfigMap, rabbitmq))));
    // Here we first prove spec |= []helper_invariants::cm_rv_stays_unchanged(rabbitmq) using invariant_n
    // This requires us to first prove spec |= true ~> []sub_resource_state_matches(SubResource::ServerConfigMap, rabbitmq), which is from the precondition
    always_tla_forall_apply_for_sub_resource(spec, SubResource::ServerConfigMap, rabbitmq);
    let spec_action = |s: RMQCluster, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight_of(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& sub_resource_state_matches(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::ServerConfigMap, rabbitmq)(s)
    };
    invariant_n!(
        spec, lift_action(spec_action), lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq)),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight_of(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(sub_resource_state_matches(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::ServerConfigMap, rabbitmq))
    );
    // Now we will use the invariant helper_invariants::cm_rv_stays_unchanged(rabbitmq) to call lemma_stateful_set_is_stable
    always_tla_forall_apply_for_sub_resource(spec, SubResource::StatefulSet, rabbitmq);
    entails_trans(spec, assumption_and_invariants_of_all_phases(rabbitmq), true_pred().leads_to(lift_state(sub_resource_state_matches(SubResource::StatefulSet, rabbitmq))));
    lemma_stateful_set_is_stable(spec, rabbitmq, true_pred());
    assumption_and_invariants_of_all_phases_is_stable(rabbitmq);
    unpack_conditions_from_spec(assumption_and_invariants_of_all_phases(rabbitmq), always(lift_state(sub_resource_state_matches(SubResource::ServerConfigMap, rabbitmq))), true_pred(), always(lift_state(sub_resource_state_matches(SubResource::StatefulSet, rabbitmq))));
    temp_pred_equality(always(lift_state(sub_resource_state_matches(SubResource::ServerConfigMap, rabbitmq))), true_pred().and(always(lift_state(sub_resource_state_matches(SubResource::ServerConfigMap, rabbitmq)))));
    leads_to_trans_temp(assumption_and_invariants_of_all_phases(rabbitmq), true_pred(), always(lift_state(sub_resource_state_matches(SubResource::ServerConfigMap, rabbitmq))), always(lift_state(sub_resource_state_matches(SubResource::StatefulSet, rabbitmq))))
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
    RMQCluster::lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec(spec, input, RMQCluster::next(), RMQCluster::desired_state_is(rabbitmq), pre, post);
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
    RMQCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, RMQCluster::run_scheduled_reconcile(), pre, post);
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
                .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::HeadlessService, rabbitmq)))
        ),
{
    let pre = no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::Init);
    let post = pending_req_in_flight_at_after_get_resource_step(SubResource::HeadlessService, rabbitmq);
    let input = (None, Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(RMQCluster::next()), lift_state(RMQCluster::crash_disabled())
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

proof fn always_tla_forall_apply_for_sub_resource(spec: TempPred<RMQCluster>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of(res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, rabbitmq))))),
    ensures
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_of(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)))),
{
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, rabbitmq)), sub_resource);
}

}
