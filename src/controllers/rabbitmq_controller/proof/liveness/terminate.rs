// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, prelude::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep, ReconcileLocalState},
    message::*,
};
use crate::rabbitmq_controller::{
    model::{install::*, reconciler::*},
    proof::predicate::*,
    trusted::{spec_types::*, step::*},
};
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// Trigger function for assertions
pub uninterp spec fn dummy<T>(t: T) -> bool;

pub open spec fn at_step_state_pred(rabbitmq: RabbitmqClusterView, controller_id: int, step: RabbitmqReconcileStep) -> StatePred<ClusterState> {
    Cluster::at_expected_reconcile_states(controller_id, rabbitmq.object_ref(), |s: ReconcileLocalState| {
        let state = RabbitmqReconcileState::unmarshal(s).unwrap();
        state.reconcile_step == step
    })
}

pub open spec fn state_pred_regarding_sub_resource(rabbitmq: RabbitmqClusterView, controller_id: int, sub_resource: SubResource) -> StatePred<ClusterState> {
    Cluster::at_expected_reconcile_states(
        controller_id,
        rabbitmq.object_ref(),
        |s: ReconcileLocalState| {
            let state = RabbitmqReconcileState::unmarshal(s).unwrap();
            state.reconcile_step is AfterKRequestStep && state.reconcile_step->AfterKRequestStep_1 == sub_resource
        }
    )
}

proof fn lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, rabbitmq: RabbitmqClusterView, sub_resource: SubResource, next_step: RabbitmqReconcileStep
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        // Ensures that after get/create/update the sub resource, there is always a pending request or matched response
        // in flight so that the reconciler can enter the next state.
        forall |action: ActionKind| #![auto]
            spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(action, sub_resource)
            ))))),
        // Ensures that after successfully creating or updating the sub resource, the reconcile will go to after get next
        // sub resource step.
        next_resource_after(sub_resource) == next_step,
        spec.entails(lift_state(at_step_state_pred(rabbitmq, controller_id, next_step))
            .leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))),
        spec.entails(lift_state(at_step_state_pred(rabbitmq, controller_id, RabbitmqReconcileStep::Error))
            .leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))),
    ensures
        spec.entails(lift_state(at_step_state_pred(rabbitmq, controller_id, after_get_k_request_step(sub_resource)))
            .leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))),
        spec.entails(lift_state(state_pred_regarding_sub_resource(rabbitmq, controller_id, sub_resource))
            .leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))),
{
    RabbitmqReconcileState::marshal_preserves_integrity();
    let state_after_create_or_update = |s: ReconcileLocalState| {
        let state = RabbitmqReconcileState::unmarshal(s).unwrap();
        state.reconcile_step == next_step
        || state.reconcile_step == RabbitmqReconcileStep::Error
    };
    or_leads_to_combine_and_equality!(
        spec, lift_state(Cluster::at_expected_reconcile_states(controller_id, rabbitmq.object_ref(), state_after_create_or_update)),
        lift_state(at_step_state_pred(rabbitmq, controller_id, next_step)),
        lift_state(at_step_state_pred(rabbitmq, controller_id, RabbitmqReconcileStep::Error));
        lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref()) })
    );
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, rabbitmq.object_ref(), at_step_closure(after_create_k_request_step(sub_resource)), state_after_create_or_update);
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, rabbitmq.object_ref(), at_step_closure(after_update_k_request_step(sub_resource)), state_after_create_or_update);

    let state_after_get = |s: ReconcileLocalState| {
        let state = RabbitmqReconcileState::unmarshal(s).unwrap();
        state.reconcile_step == after_create_k_request_step(sub_resource)
        || state.reconcile_step == after_update_k_request_step(sub_resource)
        || state.reconcile_step == RabbitmqReconcileStep::Error
    };
    or_leads_to_combine_and_equality!(
        spec, lift_state(Cluster::at_expected_reconcile_states(controller_id, rabbitmq.object_ref(), state_after_get)),
        lift_state(at_step_state_pred(rabbitmq, controller_id, after_create_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(rabbitmq, controller_id, after_update_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(rabbitmq, controller_id, RabbitmqReconcileStep::Error));
        lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref()) })
    );
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, rabbitmq.object_ref(), at_step_closure(after_get_k_request_step(sub_resource)), state_after_get);
    or_leads_to_combine_and_equality!(
        spec, lift_state(state_pred_regarding_sub_resource(rabbitmq, controller_id, sub_resource)),
        lift_state(at_step_state_pred(rabbitmq, controller_id, after_get_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(rabbitmq, controller_id, after_create_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(rabbitmq, controller_id, after_update_k_request_step(sub_resource)));
        lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref()) })
    );
}

pub proof fn reconcile_eventually_terminates(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
            controller_id, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::Init))))),
        spec.entails(always(tla_forall(|step: (ActionKind, SubResource)| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.0, step.1))
            ))))),
    ensures spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))),
{
    RabbitmqReconcileState::marshal_preserves_integrity();
    assert forall |action: ActionKind, sub_resource: SubResource| #![auto]
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(action, sub_resource))
    )))) by {
        always_tla_forall_apply::<ClusterState, (ActionKind, SubResource)>(
            spec, |step: (ActionKind, SubResource)| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.0, step.1))
            )), (action, sub_resource)
        );
    }
    let reconcile_idle = |s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref()) };

    // First, prove that reconcile_done \/ reconcile_error \/ reconcile_idle ~> reconcile_idle.
    // Here we simply apply a cluster lemma which uses the wf1 of end_reconcile action.
    cluster.lemma_reconcile_error_leads_to_reconcile_idle(spec, controller_id, rabbitmq.object_ref());
    cluster.lemma_reconcile_done_leads_to_reconcile_idle(spec, controller_id, rabbitmq.object_ref());
    temp_pred_equality(lift_state(at_step_state_pred(rabbitmq, controller_id, RabbitmqReconcileStep::Done)), lift_state(cluster.reconciler_reconcile_done(controller_id, rabbitmq.object_ref())));
    temp_pred_equality(lift_state(at_step_state_pred(rabbitmq, controller_id, RabbitmqReconcileStep::Error)), lift_state(cluster.reconciler_reconcile_error(controller_id, rabbitmq.object_ref())));
    entails_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));

    // Second, prove that the sub resource that every intermediate steps can lead to reconcile idle.
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, cluster, controller_id, rabbitmq, SubResource::StatefulSet, RabbitmqReconcileStep::Done);
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, cluster, controller_id, rabbitmq, SubResource::RoleBinding, after_get_k_request_step(SubResource::StatefulSet));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, cluster, controller_id, rabbitmq, SubResource::Role, after_get_k_request_step(SubResource::RoleBinding));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, cluster, controller_id, rabbitmq, SubResource::ServiceAccount, after_get_k_request_step(SubResource::Role));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, cluster, controller_id, rabbitmq, SubResource::ServerConfigMap, after_get_k_request_step(SubResource::ServiceAccount));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, cluster, controller_id, rabbitmq, SubResource::PluginsConfigMap, after_get_k_request_step(SubResource::ServerConfigMap));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, cluster, controller_id, rabbitmq, SubResource::DefaultUserSecret, after_get_k_request_step(SubResource::PluginsConfigMap));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, cluster, controller_id, rabbitmq, SubResource::ErlangCookieSecret, after_get_k_request_step(SubResource::DefaultUserSecret));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, cluster, controller_id, rabbitmq, SubResource::Service, after_get_k_request_step(SubResource::ErlangCookieSecret));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, cluster, controller_id, rabbitmq, SubResource::HeadlessService, after_get_k_request_step(SubResource::Service));

    // Third, prove that reconcile init state can reach the state of handling the first sub resource (headless service).
    cluster.lemma_from_init_state_to_next_state_to_reconcile_idle(spec, controller_id, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::Init), at_step_closure(after_get_k_request_step(SubResource::HeadlessService)));

    // Finally, combine all cases.
    or_leads_to_combine_and_equality!(
        spec,
        true_pred(),
        lift_state(reconcile_idle),
        lift_state(at_step_state_pred(rabbitmq, controller_id, RabbitmqReconcileStep::Init)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, controller_id, SubResource::HeadlessService)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, controller_id, SubResource::Service)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, controller_id, SubResource::ErlangCookieSecret)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, controller_id, SubResource::DefaultUserSecret)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, controller_id, SubResource::PluginsConfigMap)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, controller_id, SubResource::ServerConfigMap)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, controller_id, SubResource::ServiceAccount)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, controller_id, SubResource::Role)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, controller_id, SubResource::RoleBinding)),
        lift_state(state_pred_regarding_sub_resource(rabbitmq, controller_id, SubResource::StatefulSet)),
        lift_state(at_step_state_pred(rabbitmq, controller_id, RabbitmqReconcileStep::Done)),
        lift_state(at_step_state_pred(rabbitmq, controller_id, RabbitmqReconcileStep::Error));
        lift_state(reconcile_idle)
    );
}

}
