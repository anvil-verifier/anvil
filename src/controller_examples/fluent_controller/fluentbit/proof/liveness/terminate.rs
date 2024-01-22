// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::EmptyAPI;
use crate::fluent_controller::fluentbit::{
    model::{reconciler::*, resource::*},
    proof::predicate::*,
    trusted::{spec_types::*, step::*},
};
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

pub proof fn reconcile_eventually_terminates(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::external_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCluster::pending_req_of_key_is_unique_with_unique_id(fb.object_ref())))),
        spec.entails(always(lift_state(FBCluster::no_pending_req_msg_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::Init))))),
        spec.entails(always(lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterGetSecret))))),
        spec.entails(always(tla_forall(|step: (ActionKind, SubResource)| lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterKRequestStep(step.0, step.1))
        ))))),
    ensures spec.entails(true_pred().leads_to(lift_state(|s: FBCluster| !s.ongoing_reconciles().contains_key(fb.object_ref())))),
{
    assert forall |action: ActionKind, sub_resource: SubResource| #![auto]
    spec.entails(always(lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterKRequestStep(action, sub_resource))
    )))) by {
        always_tla_forall_apply::<FBCluster, (ActionKind, SubResource)>(
            spec, |step: (ActionKind, SubResource)| lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterKRequestStep(step.0, step.1))
            )), (action, sub_resource)
        );
    }
    let reconcile_idle = |s: FBCluster| { !s.ongoing_reconciles().contains_key(fb.object_ref()) };

    // First, prove that reconcile_done \/ reconcile_error \/ reconcile_ide ~> reconcile_idle.
    // Here we simply apply a cluster lemma which uses the wf1 of end_reconcile action.
    FBCluster::lemma_reconcile_error_leads_to_reconcile_idle(spec, fb.object_ref());
    FBCluster::lemma_reconcile_done_leads_to_reconcile_idle(spec, fb.object_ref());
    temp_pred_equality(lift_state(at_step_state_pred(fb, FluentBitReconcileStep::Done)), lift_state(FBCluster::reconciler_reconcile_done(fb.object_ref())));
    temp_pred_equality(lift_state(at_step_state_pred(fb, FluentBitReconcileStep::Error)), lift_state(FBCluster::reconciler_reconcile_error(fb.object_ref())));
    valid_implies_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));

    // Second, prove that the sub resource that every intermediate steps can lead to reconcile idle.
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, fb, SubResource::DaemonSet, FluentBitReconcileStep::Done);
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, fb, SubResource::Service, after_get_k_request_step(SubResource::DaemonSet));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, fb, SubResource::RoleBinding, after_get_k_request_step(SubResource::Service));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, fb, SubResource::Role, after_get_k_request_step(SubResource::RoleBinding));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, fb, SubResource::ServiceAccount, after_get_k_request_step(SubResource::Role));

    // Third, prove that after get secret step can reach the state of handling the first sub resource (service account).
    or_leads_to_combine_and_equality!(
        spec,
        lift_state(at_step1_or_step2_state_pred(fb, after_get_k_request_step(SubResource::ServiceAccount), FluentBitReconcileStep::Error)),
        lift_state(at_step_state_pred(fb, after_get_k_request_step(SubResource::ServiceAccount))),
        lift_state(at_step_state_pred(fb, FluentBitReconcileStep::Error));
        lift_state(reconcile_idle)
    );
    FBCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, fb, at_step_closure(FluentBitReconcileStep::AfterGetSecret),
        at_step1_or_step2_closure(after_get_k_request_step(SubResource::ServiceAccount), FluentBitReconcileStep::Error)
    );

    // Fourth, prove that reconcile init state can reach the state after get secret.
    FBCluster::lemma_from_init_state_to_next_state_to_reconcile_idle(spec, fb, at_step_closure(FluentBitReconcileStep::Init), at_step_closure(FluentBitReconcileStep::AfterGetSecret));

    // Finally, combine all cases.
    or_leads_to_combine_and_equality!(
        spec,
        true_pred(),
        lift_state(reconcile_idle),
        lift_state(at_step_state_pred(fb, FluentBitReconcileStep::Init)),
        lift_state(at_step_state_pred(fb, FluentBitReconcileStep::AfterGetSecret)),
        lift_state(state_pred_regarding_sub_resource(fb, SubResource::ServiceAccount)),
        lift_state(state_pred_regarding_sub_resource(fb, SubResource::Role)),
        lift_state(state_pred_regarding_sub_resource(fb, SubResource::RoleBinding)),
        lift_state(state_pred_regarding_sub_resource(fb, SubResource::Service)),
        lift_state(state_pred_regarding_sub_resource(fb, SubResource::DaemonSet)),
        lift_state(at_step_state_pred(fb, FluentBitReconcileStep::Done)),
        lift_state(at_step_state_pred(fb, FluentBitReconcileStep::Error));
        lift_state(reconcile_idle)
    );
}

pub open spec fn at_step_state_pred(fb: FluentBitView, step: FluentBitReconcileStep) -> StatePred<FBCluster> {
    FBCluster::at_expected_reconcile_states(fb.object_ref(), |s: FluentBitReconcileState| s.reconcile_step == step)
}

pub open spec fn at_step1_or_step2_state_pred(fb: FluentBitView, step1: FluentBitReconcileStep, step2: FluentBitReconcileStep) -> StatePred<FBCluster> {
    FBCluster::at_expected_reconcile_states(fb.object_ref(), |s: FluentBitReconcileState| s.reconcile_step == step1 || s.reconcile_step == step2)
}

pub open spec fn state_pred_regarding_sub_resource(fb: FluentBitView, sub_resource: SubResource) -> StatePred<FBCluster> {
    FBCluster::at_expected_reconcile_states(
        fb.object_ref(),
        |s: FluentBitReconcileState| s.reconcile_step.is_AfterKRequestStep() && s.reconcile_step.get_AfterKRequestStep_1() == sub_resource
    )
}

proof fn lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(
    spec: TempPred<FBCluster>, fb: FluentBitView, sub_resource: SubResource, next_step: FluentBitReconcileStep
)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::external_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCluster::pending_req_of_key_is_unique_with_unique_id(fb.object_ref())))),
        // Ensures that after get/create/update the sub resource, there is always a pending request or matched response
        // in flight so that the reconciler can enter the next state.
        forall |action: ActionKind| #![auto]
            spec.entails(always(lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterKRequestStep(action, sub_resource)
            ))))),
        // Ensures that after successfully creating or updating the sub resource, the reconcile will go to after get next
        // sub resource step.
        next_resource_after(sub_resource) == next_step,
        spec.entails(lift_state(at_step_state_pred(fb, next_step))
            .leads_to(lift_state(|s: FBCluster| !s.ongoing_reconciles().contains_key(fb.object_ref())))),
        spec.entails(lift_state(at_step_state_pred(fb, FluentBitReconcileStep::Error))
            .leads_to(lift_state(|s: FBCluster| !s.ongoing_reconciles().contains_key(fb.object_ref())))),
    ensures
        spec.entails(lift_state(at_step_state_pred(fb, after_get_k_request_step(sub_resource))).leads_to(lift_state(|s: FBCluster| !s.ongoing_reconciles().contains_key(fb.object_ref())))),
        spec.entails(lift_state(state_pred_regarding_sub_resource(fb, sub_resource)).leads_to(lift_state(|s: FBCluster| !s.ongoing_reconciles().contains_key(fb.object_ref())))),
{
    hide(make_daemon_set);
    let state_after_create_or_update = |s: FluentBitReconcileState| {
        s.reconcile_step == next_step
        || s.reconcile_step == FluentBitReconcileStep::Error
    };
    or_leads_to_combine_and_equality!(
        spec, lift_state(FBCluster::at_expected_reconcile_states(fb.object_ref(), state_after_create_or_update)),
        lift_state(at_step_state_pred(fb, next_step)),
        lift_state(at_step_state_pred(fb, FluentBitReconcileStep::Error));
        lift_state(|s: FBCluster| { !s.ongoing_reconciles().contains_key(fb.object_ref()) })
    );
    FBCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, fb, at_step_closure(after_create_k_request_step(sub_resource)), state_after_create_or_update);
    FBCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, fb, at_step_closure(after_update_k_request_step(sub_resource)), state_after_create_or_update);

    let state_after_get = |s: FluentBitReconcileState| {
        s.reconcile_step == after_create_k_request_step(sub_resource)
        || s.reconcile_step == after_update_k_request_step(sub_resource)
        || s.reconcile_step == FluentBitReconcileStep::Error
    };
    or_leads_to_combine_and_equality!(
        spec, lift_state(FBCluster::at_expected_reconcile_states(fb.object_ref(), state_after_get)),
        lift_state(at_step_state_pred(fb, after_create_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(fb, after_update_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(fb, FluentBitReconcileStep::Error));
        lift_state(|s: FBCluster| { !s.ongoing_reconciles().contains_key(fb.object_ref()) })
    );
    FBCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, fb, at_step_closure(after_get_k_request_step(sub_resource)), state_after_get);
    or_leads_to_combine_and_equality!(
        spec, lift_state(state_pred_regarding_sub_resource(fb, sub_resource)),
        lift_state(at_step_state_pred(fb, after_get_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(fb, after_create_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(fb, after_update_k_request_step(sub_resource)));
        lift_state(|s: FBCluster| { !s.ongoing_reconciles().contains_key(fb.object_ref()) })
    );
}

}
