// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::EmptyAPI;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    model::reconciler::*,
    proof::predicate::*,
    trusted::{spec_types::*, step::*},
};
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

pub proof fn reconcile_eventually_terminates(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::external_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::pending_req_of_key_is_unique_with_unique_id(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::no_pending_req_msg_at_reconcile_state(
            rabbitmq.object_ref(), |s: RabbitmqReconcileState| s.reconcile_step == RabbitmqReconcileStep::Init)))),
        spec.entails(always(tla_forall(|step: (ActionKind, SubResource)| lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.0, step.1))
            ))))),
    ensures spec.entails(true_pred().leads_to(lift_state(|s: RMQCluster| !s.ongoing_reconciles().contains_key(rabbitmq.object_ref())))),
{
    assert forall |action: ActionKind, sub_resource: SubResource| #![auto]
    spec.entails(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(action, sub_resource))
    )))) by {
        always_tla_forall_apply::<RMQCluster, (ActionKind, SubResource)>(
            spec, |step: (ActionKind, SubResource)| lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.0, step.1))
            )), (action, sub_resource)
        );
    }
    let reconcile_idle = |s: RMQCluster| { !s.ongoing_reconciles().contains_key(rabbitmq.object_ref()) };

    // First, prove that reconcile_done \/ reconcile_error \/ reconcile_ide ~> reconcile_idle.
    // Here we simply apply a cluster lemma which uses the wf1 of end_reconcile action.
    RMQCluster::lemma_reconcile_error_leads_to_reconcile_idle(spec, rabbitmq.object_ref());
    RMQCluster::lemma_reconcile_done_leads_to_reconcile_idle(spec, rabbitmq.object_ref());
    temp_pred_equality(lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Done)), lift_state(RMQCluster::reconciler_reconcile_done(rabbitmq.object_ref())));
    temp_pred_equality(lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Error)), lift_state(RMQCluster::reconciler_reconcile_error(rabbitmq.object_ref())));
    valid_implies_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));

    // Second, prove that the sub resource that every intermediate steps can lead to reconcile idle.
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, rabbitmq, SubResource::StatefulSet, RabbitmqReconcileStep::Done);
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, rabbitmq, SubResource::RoleBinding, after_get_k_request_step(SubResource::StatefulSet));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, rabbitmq, SubResource::Role, after_get_k_request_step(SubResource::RoleBinding));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, rabbitmq, SubResource::ServiceAccount, after_get_k_request_step(SubResource::Role));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, rabbitmq, SubResource::ServerConfigMap, after_get_k_request_step(SubResource::ServiceAccount));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, rabbitmq, SubResource::PluginsConfigMap, after_get_k_request_step(SubResource::ServerConfigMap));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, rabbitmq, SubResource::DefaultUserSecret, after_get_k_request_step(SubResource::PluginsConfigMap));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, rabbitmq, SubResource::ErlangCookieSecret, after_get_k_request_step(SubResource::DefaultUserSecret));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, rabbitmq, SubResource::Service, after_get_k_request_step(SubResource::ErlangCookieSecret));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, rabbitmq, SubResource::HeadlessService, after_get_k_request_step(SubResource::Service));

    // Third, prove that reconcile init state can reach the state of handling the first sub resource (headless service).
    RMQCluster::lemma_from_init_state_to_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::Init), at_step_closure(after_get_k_request_step(SubResource::HeadlessService)));

    // Finally, combine all cases.
    or_leads_to_combine_and_equality!(
        spec,
        true_pred(),
        lift_state(reconcile_idle),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Init)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, SubResource::HeadlessService)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, SubResource::Service)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, SubResource::ErlangCookieSecret)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, SubResource::DefaultUserSecret)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, SubResource::PluginsConfigMap)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, SubResource::ServerConfigMap)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, SubResource::ServiceAccount)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, SubResource::Role)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, SubResource::RoleBinding)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, SubResource::StatefulSet)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Done)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Error));
        lift_state(reconcile_idle)
    );
}

pub open spec fn at_step_state_pred(rabbitmq: RabbitmqClusterView, step: RabbitmqReconcileStep) -> StatePred<RMQCluster> {
    RMQCluster::at_expected_reconcile_states(rabbitmq.object_ref(), |s: RabbitmqReconcileState| s.reconcile_step == step)
}

pub open spec fn state_pred_regarding_sub_resource(rabbitmq: RabbitmqClusterView, sub_resource: SubResource) -> StatePred<RMQCluster> {
    RMQCluster::at_expected_reconcile_states(
        rabbitmq.object_ref(),
        |s: RabbitmqReconcileState| s.reconcile_step.is_AfterKRequestStep() && s.reconcile_step.get_AfterKRequestStep_1() == sub_resource
    )
}

proof fn lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, sub_resource: SubResource, next_step: RabbitmqReconcileStep
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::external_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::pending_req_of_key_is_unique_with_unique_id(rabbitmq.object_ref())))),
        // Ensures that after get/create/update the sub resource, there is always a pending request or matched response
        // in flight so that the reconciler can enter the next state.
        forall |action: ActionKind| #![auto]
            spec.entails(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(action, sub_resource)
            ))))),
        // Ensures that after successfully creating or updating the sub resource, the reconcile will go to after get next
        // sub resource step.
        next_resource_after(sub_resource) == next_step,
        spec.entails(lift_state(at_step_state_pred(rabbitmq, next_step))
            .leads_to(lift_state(|s: RMQCluster| !s.ongoing_reconciles().contains_key(rabbitmq.object_ref())))),
        spec.entails(lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Error))
            .leads_to(lift_state(|s: RMQCluster| !s.ongoing_reconciles().contains_key(rabbitmq.object_ref())))),
    ensures
        spec.entails(lift_state(at_step_state_pred(rabbitmq, after_get_k_request_step(sub_resource)))
            .leads_to(lift_state(|s: RMQCluster| !s.ongoing_reconciles().contains_key(rabbitmq.object_ref())))),
        spec.entails(lift_state(state_pred_regarding_sub_resource(rabbitmq, sub_resource))
            .leads_to(lift_state(|s: RMQCluster| !s.ongoing_reconciles().contains_key(rabbitmq.object_ref())))),
{
    let state_after_create_or_update = |s: RabbitmqReconcileState| {
        s.reconcile_step == next_step
        || s.reconcile_step == RabbitmqReconcileStep::Error
    };
    or_leads_to_combine_and_equality!(
        spec, lift_state(RMQCluster::at_expected_reconcile_states(rabbitmq.object_ref(), state_after_create_or_update)),
        lift_state(at_step_state_pred(rabbitmq, next_step)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Error));
        lift_state(|s: RMQCluster| { !s.ongoing_reconciles().contains_key(rabbitmq.object_ref()) })
    );
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(after_create_k_request_step(sub_resource)), state_after_create_or_update);
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(after_update_k_request_step(sub_resource)), state_after_create_or_update);

    let state_after_get = |s: RabbitmqReconcileState| {
        s.reconcile_step == after_create_k_request_step(sub_resource)
        || s.reconcile_step == after_update_k_request_step(sub_resource)
        || s.reconcile_step == RabbitmqReconcileStep::Error
    };
    or_leads_to_combine_and_equality!(
        spec, lift_state(RMQCluster::at_expected_reconcile_states(rabbitmq.object_ref(), state_after_get)),
        lift_state(at_step_state_pred(rabbitmq, after_create_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(rabbitmq, after_update_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Error));
        lift_state(|s: RMQCluster| { !s.ongoing_reconciles().contains_key(rabbitmq.object_ref()) })
    );
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(after_get_k_request_step(sub_resource)), state_after_get);
    or_leads_to_combine_and_equality!(
        spec, lift_state(state_pred_regarding_sub_resource(rabbitmq, sub_resource)),
        lift_state(at_step_state_pred(rabbitmq, after_get_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(rabbitmq, after_create_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(rabbitmq, after_update_k_request_step(sub_resource)));
        lift_state(|s: RMQCluster| { !s.ongoing_reconciles().contains_key(rabbitmq.object_ref()) })
    );
}

}
