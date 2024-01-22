// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::EmptyAPI;
use crate::fluent_controller::fluentbit_config::{
    model::reconciler::*,
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

pub proof fn reconcile_eventually_terminates(spec: TempPred<FBCCluster>, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::external_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::pending_req_of_key_is_unique_with_unique_id(fbc.object_ref())))),
        spec.entails(always(lift_state(FBCCluster::no_pending_req_msg_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::Init))))),
        spec.entails(always(tla_forall(|step: (ActionKind, SubResource)| lift_state(FBCCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(step.0, step.1))
        ))))),
    ensures spec.entails(true_pred().leads_to(lift_state(|s: FBCCluster| !s.ongoing_reconciles().contains_key(fbc.object_ref())))),
{
    assert forall |action: ActionKind, sub_resource: SubResource| #![auto]
    spec.entails(always(lift_state(FBCCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(action, sub_resource))
    )))) by {
        always_tla_forall_apply::<FBCCluster, (ActionKind, SubResource)>(
            spec, |step: (ActionKind, SubResource)| lift_state(FBCCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(step.0, step.1))
            )), (action, sub_resource)
        );
    }
    let reconcile_idle = |s: FBCCluster| { !s.ongoing_reconciles().contains_key(fbc.object_ref()) };

    // First, prove that reconcile_done \/ reconcile_error \/ reconcile_ide ~> reconcile_idle.
    // Here we simply apply a cluster lemma which uses the wf1 of end_reconcile action.
    FBCCluster::lemma_reconcile_error_leads_to_reconcile_idle(spec, fbc.object_ref());
    FBCCluster::lemma_reconcile_done_leads_to_reconcile_idle(spec, fbc.object_ref());
    temp_pred_equality(lift_state(at_step_state_pred(fbc, FluentBitConfigReconcileStep::Done)), lift_state(FBCCluster::reconciler_reconcile_done(fbc.object_ref())));
    temp_pred_equality(lift_state(at_step_state_pred(fbc, FluentBitConfigReconcileStep::Error)), lift_state(FBCCluster::reconciler_reconcile_error(fbc.object_ref())));
    valid_implies_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));

    // Second, prove that the sub resource that every intermediate steps can lead to reconcile idle.
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, fbc, SubResource::Secret, FluentBitConfigReconcileStep::Done);

    // Third, prove that reconcile init state can reach the state after get secret.
    FBCCluster::lemma_from_init_state_to_next_state_to_reconcile_idle(spec, fbc, at_step_closure(FluentBitConfigReconcileStep::Init), at_step_closure(after_get_k_request_step(SubResource::Secret)));

    // Finally, combine all cases.
    or_leads_to_combine_and_equality!(
        spec,
        true_pred(),
        lift_state(reconcile_idle),
        lift_state(at_step_state_pred(fbc, FluentBitConfigReconcileStep::Init)),
        lift_state(state_pred_regarding_sub_resource(fbc, SubResource::Secret)),
        lift_state(at_step_state_pred(fbc, FluentBitConfigReconcileStep::Done)),
        lift_state(at_step_state_pred(fbc, FluentBitConfigReconcileStep::Error));
        lift_state(reconcile_idle)
    );
}

pub open spec fn at_step_state_pred(fbc: FluentBitConfigView, step: FluentBitConfigReconcileStep) -> StatePred<FBCCluster> {
    FBCCluster::at_expected_reconcile_states(fbc.object_ref(), |s: FluentBitConfigReconcileState| s.reconcile_step == step)
}

pub open spec fn state_pred_regarding_sub_resource(fbc: FluentBitConfigView, sub_resource: SubResource) -> StatePred<FBCCluster> {
    FBCCluster::at_expected_reconcile_states(
        fbc.object_ref(),
        |s: FluentBitConfigReconcileState| s.reconcile_step.is_AfterKRequestStep() && s.reconcile_step.get_AfterKRequestStep_1() == sub_resource
    )
}

proof fn lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(
    spec: TempPred<FBCCluster>, fbc: FluentBitConfigView, sub_resource: SubResource, next_step: FluentBitConfigReconcileStep
)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::external_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::pending_req_of_key_is_unique_with_unique_id(fbc.object_ref())))),
        // Ensures that after get/create/update the sub resource, there is always a pending request or matched response
        // in flight so that the reconciler can enter the next state.
        forall |action: ActionKind| #![auto]
            spec.entails(always(lift_state(FBCCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(action, sub_resource)
            ))))),
        // Ensures that after successfully creating or updating the sub resource, the reconcile will go to after get next
        // sub resource step.
        next_resource_after(sub_resource) == next_step,
        spec.entails(lift_state(at_step_state_pred(fbc, next_step)).leads_to(lift_state(|s: FBCCluster| !s.ongoing_reconciles().contains_key(fbc.object_ref())))),
        spec.entails(lift_state(at_step_state_pred(fbc, FluentBitConfigReconcileStep::Error)).leads_to(lift_state(|s: FBCCluster| !s.ongoing_reconciles().contains_key(fbc.object_ref())))),
    ensures
        spec.entails(lift_state(at_step_state_pred(fbc, after_get_k_request_step(sub_resource))).leads_to(lift_state(|s: FBCCluster| !s.ongoing_reconciles().contains_key(fbc.object_ref())))),
        spec.entails(lift_state(state_pred_regarding_sub_resource(fbc, sub_resource)).leads_to(lift_state(|s: FBCCluster| !s.ongoing_reconciles().contains_key(fbc.object_ref())))),
{
    let state_after_create_or_update = |s: FluentBitConfigReconcileState| {
        s.reconcile_step == next_step
        || s.reconcile_step == FluentBitConfigReconcileStep::Error
    };
    or_leads_to_combine_and_equality!(
        spec, lift_state(FBCCluster::at_expected_reconcile_states(fbc.object_ref(), state_after_create_or_update)),
        lift_state(at_step_state_pred(fbc, next_step)),
        lift_state(at_step_state_pred(fbc, FluentBitConfigReconcileStep::Error));
        lift_state(|s: FBCCluster| { !s.ongoing_reconciles().contains_key(fbc.object_ref()) })
    );
    FBCCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, fbc, at_step_closure(after_create_k_request_step(sub_resource)), state_after_create_or_update);
    FBCCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, fbc, at_step_closure(after_update_k_request_step(sub_resource)), state_after_create_or_update);

    let state_after_get = |s: FluentBitConfigReconcileState| {
        s.reconcile_step == after_create_k_request_step(sub_resource)
        || s.reconcile_step == after_update_k_request_step(sub_resource)
        || s.reconcile_step == FluentBitConfigReconcileStep::Error
    };
    or_leads_to_combine_and_equality!(
        spec, lift_state(FBCCluster::at_expected_reconcile_states(fbc.object_ref(), state_after_get)),
        lift_state(at_step_state_pred(fbc, after_create_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(fbc, after_update_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(fbc, FluentBitConfigReconcileStep::Error));
        lift_state(|s: FBCCluster| { !s.ongoing_reconciles().contains_key(fbc.object_ref()) })
    );
    FBCCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, fbc, at_step_closure(after_get_k_request_step(sub_resource)), state_after_get);
    or_leads_to_combine_and_equality!(
        spec, lift_state(state_pred_regarding_sub_resource(fbc, sub_resource)),
        lift_state(at_step_state_pred(fbc, after_get_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(fbc, after_create_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(fbc, after_update_k_request_step(sub_resource)));
        lift_state(|s: FBCCluster| { !s.ongoing_reconciles().contains_key(fbc.object_ref()) })
    );
}

}
