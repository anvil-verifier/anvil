// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::rabbitmq_controller::model::install::rabbitmq_controller_model;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    model::{reconciler::*, resource::*},
    proof::{
        helper_invariants,
        liveness::{
            resource_match::*,
            spec::*,
            // stateful_set_match::{
            //     lemma_from_after_get_stateful_set_step_to_stateful_set_matches,
            //     lemma_stateful_set_is_stable,
            // },
            terminate,
        },
        predicate::*,
        resource::*,
    },
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{map_lib::*, string_view::*};
use vstd::{prelude::*, string::*};

verus! {

proof fn liveness_proof(cluster: Cluster, controller_id: int, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures spec.entails(always(lift_state(current_state_matches(rabbitmq)))),
{
    assumption_and_invariants_of_all_phases_is_stable(controller_id, cluster, rabbitmq);
    lemma_true_leads_to_always_current_state_matches(controller_id, cluster, rabbitmq);
    reveal_with_fuel(spec_before_phase_n, 8);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(controller_id, cluster, 7, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(controller_id, cluster, 6, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(controller_id, cluster, 5, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(controller_id, cluster, 4, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(controller_id, cluster, 3, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(controller_id, cluster, 2, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(controller_id, cluster, 1, rabbitmq);

    let assumption = always(lift_state(Cluster::desired_state_is(rabbitmq)));
    unpack_conditions_from_spec(invariants(controller_id, cluster, rabbitmq), assumption, true_pred(), always(lift_state(current_state_matches(rabbitmq))));
    temp_pred_equality(true_pred().and(assumption), assumption);

    entails_trans(
        spec.and(derived_invariants_since_beginning(controller_id, cluster, rabbitmq)), invariants(controller_id, cluster, rabbitmq),
        always(lift_state(Cluster::desired_state_is(rabbitmq))).leads_to(always(lift_state(current_state_matches(rabbitmq))))
    );
    sm_spec_entails_all_invariants(controller_id, cluster, spec, rabbitmq);
    simplify_predicate(spec, derived_invariants_since_beginning(controller_id, cluster, rabbitmq));
}

proof fn spec_before_phase_n_entails_true_leads_to_current_state_matches(controller_id: int, cluster: Cluster, i: nat, rabbitmq: RabbitmqClusterView)
    requires
        1 <= i <= 7,
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        valid(stable(spec_before_phase_n(controller_id, i, cluster, rabbitmq))),
        spec_before_phase_n(controller_id, i + 1, cluster, rabbitmq).entails(true_pred().leads_to(always(lift_state(current_state_matches(rabbitmq)))))
    ensures spec_before_phase_n(controller_id, i, cluster, rabbitmq).entails(true_pred().leads_to(always(lift_state(current_state_matches(rabbitmq))))),
{
    reveal_with_fuel(spec_before_phase_n, 8);
    temp_pred_equality(spec_before_phase_n(controller_id, i + 1, cluster, rabbitmq), spec_before_phase_n(controller_id, i, cluster, rabbitmq).and(invariants_since_phase_n(controller_id, i, cluster, rabbitmq)));
    spec_of_previous_phases_entails_eventually_new_invariants(controller_id, cluster, i, rabbitmq);
    unpack_conditions_from_spec(spec_before_phase_n(controller_id, i, cluster, rabbitmq), invariants_since_phase_n(controller_id, i, cluster, rabbitmq), true_pred(), always(lift_state(current_state_matches(rabbitmq))));
    temp_pred_equality(true_pred().and(invariants_since_phase_n(controller_id, i, cluster, rabbitmq)), invariants_since_phase_n(controller_id, i, cluster, rabbitmq));
    leads_to_trans(spec_before_phase_n(controller_id, i, cluster, rabbitmq), true_pred(), invariants_since_phase_n(controller_id, i, cluster, rabbitmq), always(lift_state(current_state_matches(rabbitmq))));
}

proof fn lemma_true_leads_to_always_current_state_matches(controller_id: int, cluster: Cluster, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq).entails(true_pred().leads_to(always(lift_state(current_state_matches(rabbitmq))))),
{
    let spec = assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq);
    lemma_true_leads_to_always_state_matches_for_all_resources(cluster, controller_id, rabbitmq);
    let a_to_p = |res: SubResource| lift_state(resource_state_matches(res, rabbitmq));
    helper_invariants::leads_to_always_tla_forall_subresource(spec, true_pred(), a_to_p);
    assert forall |ex| #[trigger] tla_forall(a_to_p).satisfied_by(ex) implies lift_state(current_state_matches(rabbitmq)).satisfied_by(ex) by {
        let s = ex.head();
        assert forall |res: SubResource| #[trigger] resource_state_matches(res, rabbitmq)(s) by {
            tla_forall_apply(a_to_p, res);
            assert(a_to_p(res).satisfied_by(ex));
            assert(resource_state_matches(res, rabbitmq)(s));
        }
    }
    temp_pred_equality(tla_forall(|res: SubResource| lift_state(resource_state_matches(res, rabbitmq))), lift_state(current_state_matches(rabbitmq)));
}

proof fn lemma_true_leads_to_always_state_matches_for_all_resources(cluster: Cluster, controller_id: int, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        forall |sub_resource: SubResource|
            assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)
            .entails(true_pred().leads_to(always(lift_state(#[trigger] resource_state_matches(sub_resource, rabbitmq))))),
{
    lemma_true_leads_to_always_state_matches_for_all(cluster, controller_id, rabbitmq);
}

proof fn lemma_true_leads_to_always_state_matches_for_all(cluster: Cluster, controller_id: int, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        forall |sub_resource: SubResource|
            assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq).entails(true_pred().leads_to(always(lift_state(#[trigger] resource_state_matches(sub_resource, rabbitmq))))),
{
    let spec = assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq);

    assert forall |action: ActionKind, sub_resource: SubResource| #![auto] spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(action, sub_resource)))))) by {
        always_tla_forall_apply(spec, |step: (ActionKind, SubResource)| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.0, step.1)))), (action, sub_resource));
    }

    // The use of termination property ensures spec |= true ~> reconcile_idle.
    terminate::reconcile_eventually_terminates(spec, cluster, controller_id, rabbitmq);
    // Then we can continue to show that spec |= reconcile_idle ~> []current_state_matches(rabbitmq).

    // The following two lemmas show that spec |= reconcile_idle ~> init /\ no_pending_req.
    lemma_from_reconcile_idle_to_scheduled(controller_id, cluster, spec, rabbitmq);
    lemma_from_scheduled_to_init_step(controller_id, cluster, spec, rabbitmq);

    // After applying this lemma, we get spec |= init /\ no_pending_req ~> create_headless_service /\ pending_req.
    lemma_from_init_step_to_after_create_headless_service_step(controller_id, cluster, spec, rabbitmq);

    // always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(res, rabbitmq)), SubResource::ServerConfigMap);

    // We first show that the reconciler can go to at_after_get_resource_step(next_resource) from at_after_get_resource_step(sub_resource)
    // where sub_resource cannot be StatefulSet because it's the last resource to be processed and doesn't have its next_resource.
    // Through this, we can string all the resources together in sequence. This also means that the system can go to any
    // at_after_get_resource_step(sub_resource) from an arbitrary state.
    assert forall |sub_resource: SubResource| sub_resource != SubResource::VStatefulSetView implies
    spec.entails(
        lift_state(#[trigger] pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id))
            .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource_after(sub_resource)->AfterKRequestStep_1, rabbitmq, controller_id)))
    ) by {
        always_tla_forall_apply_for_sub_resource(controller_id, spec, sub_resource, rabbitmq);
        let next_resource = next_resource_after(sub_resource)->AfterKRequestStep_1;
        lemma_from_after_get_resource_step_to_resource_matches(controller_id, cluster, spec, rabbitmq, sub_resource, next_resource);
    }
    // Thanks to the recursive construction of macro.
    leads_to_trans_n!(
        spec, true_pred(), lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref()) }),
        lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref()) && s.scheduled_reconciles(controller_id).contains_key(rabbitmq.object_ref())}),
        lift_state(no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, RabbitmqReconcileStep::Init)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::HeadlessService, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::Service, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ErlangCookieSecret, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::DefaultUserSecret, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::PluginsConfigMap, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServerConfigMap, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::Role, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::RoleBinding, rabbitmq, controller_id))
    );

    // Since we already have true ~> at_after_get_resource_step(sub_resource), and we can get at_after_get_resource_step(sub_resource)
    // ~> resource_state_matches(sub_resource, rabbitmq) by applying lemma lemma_from_after_get_resource_step_to_resource_matches,
    // we now have true ~> resource_state_matches(sub_resource, rabbitmq).
    assert forall |sub_resource: SubResource| sub_resource != SubResource::VStatefulSetView implies
    spec.entails(
        true_pred().leads_to(lift_state(#[trigger] resource_state_matches(sub_resource, rabbitmq)))
    ) by {
        always_tla_forall_apply_for_sub_resource(controller_id, spec, sub_resource, rabbitmq);
        let next_resource = next_resource_after(sub_resource)->AfterKRequestStep_1;
        lemma_from_after_get_resource_step_to_resource_matches(controller_id, cluster, spec, rabbitmq, sub_resource, next_resource);
        leads_to_trans(
            spec, true_pred(), lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id)),
            lift_state(resource_state_matches(sub_resource, rabbitmq))
        );
    }

    // Now we further prove stability: given true ~> resource_state_matches(sub_resource, rabbitmq)
    // we prove true ~> []resource_state_matches(sub_resource, rabbitmq)
    assert forall |sub_resource: SubResource| sub_resource != SubResource::VStatefulSetView implies
    spec.entails(
        true_pred().leads_to(always(lift_state(#[trigger] resource_state_matches(sub_resource, rabbitmq))))
    ) by {
        always_tla_forall_apply_for_sub_resource(controller_id, spec, sub_resource, rabbitmq);
        lemma_resource_object_is_stable(controller_id, cluster, spec, sub_resource, rabbitmq, true_pred());
    }
}

proof fn lemma_from_reconcile_idle_to_scheduled(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
    ensures
        spec.entails(lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref()) })
        .leads_to(lift_state(|s: ClusterState| {
            &&& !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())
            &&& s.scheduled_reconciles(controller_id).contains_key(rabbitmq.object_ref())
        }))),
{
    let pre = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())
        &&& !s.scheduled_reconciles(controller_id).contains_key(rabbitmq.object_ref())
    };
    let post = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())
        &&& s.scheduled_reconciles(controller_id).contains_key(rabbitmq.object_ref())
    };
    let input = rabbitmq.object_ref();
    let stronger_pre = |s| {
        &&& pre(s)
        &&& Cluster::desired_state_is(rabbitmq)(s)
    };
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(rabbitmq)(s_prime)
    };
    always_to_always_later(spec, lift_state(Cluster::desired_state_is(rabbitmq)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        later(lift_state(Cluster::desired_state_is(rabbitmq)))
    );
    cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, input, stronger_next, stronger_pre, post);
    temp_pred_equality(lift_state(pre).and(lift_state(Cluster::desired_state_is(rabbitmq))), lift_state(stronger_pre));
    leads_to_by_borrowing_inv(spec, lift_state(pre), lift_state(post), lift_state(Cluster::desired_state_is(rabbitmq)));
    entails_implies_leads_to(spec, lift_state(post), lift_state(post));
    or_leads_to_combine(spec, lift_state(pre), lift_state(post), lift_state(post));
    temp_pred_equality(lift_state(pre).or(lift_state(post)), lift_state(|s: ClusterState| {!s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())}));
}

proof fn lemma_from_scheduled_to_init_step(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, rabbitmq)))),
    ensures
        spec.entails(lift_state(|s: ClusterState| {
            &&& !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())
            &&& s.scheduled_reconciles(controller_id).contains_key(rabbitmq.object_ref())
        }).leads_to(lift_state(no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, RabbitmqReconcileStep::Init)))),
{
    let pre = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())
        &&& s.scheduled_reconciles(controller_id).contains_key(rabbitmq.object_ref())
    };
    let post = no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, RabbitmqReconcileStep::Init);
    let input = (None, Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, rabbitmq)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, rabbitmq))
    );
    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::RunScheduledReconcile, pre, post);
}

proof fn lemma_from_init_step_to_after_create_headless_service_step(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
    ensures
        spec.entails(lift_state(no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, RabbitmqReconcileStep::Init))
            .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::HeadlessService, rabbitmq, controller_id)))),
{
    let pre = no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, RabbitmqReconcileStep::Init);
    let post = pending_req_in_flight_at_after_get_resource_step(SubResource::HeadlessService, rabbitmq, controller_id);
    let input = (None, Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()), lift_state(Cluster::crash_disabled(controller_id))
    );
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(input) => {
                if input.2->0 != rabbitmq.object_ref() {
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
    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post);
}

proof fn always_tla_forall_apply_for_sub_resource(controller_id: int, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(controller_id, res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_create_resource_request_msg_without_name_in_flight(res, rabbitmq))))),
    ensures
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq)))),
{
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(controller_id, res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::no_create_resource_request_msg_without_name_in_flight(res, rabbitmq)), sub_resource);
}

}
