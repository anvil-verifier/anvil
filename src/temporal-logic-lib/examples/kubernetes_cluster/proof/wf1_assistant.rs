// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::kubernetes_cluster::spec::{
    common::*,
    controller,
    controller::{controller, ControllerAction, ControllerActionInput},
    distributed_system::*,
    kubernetes_api,
    kubernetes_api::{kubernetes_api, KubernetesAPIAction, KubernetesAPIActionInput},
};
use crate::pervasive::{option::*, seq::*, set::*};
use crate::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn kubernetes_api_action_pre_implies_next_pre(action: KubernetesAPIAction, input: KubernetesAPIActionInput)
    requires
        kubernetes_api().actions.contains(action),
    ensures
        valid(lift_state(kubernetes_api_action_pre(action, input)).implies(lift_state(kubernetes_api_next().pre(input)))),
{
    assert forall |s| #[trigger] state_pred_call(kubernetes_api_action_pre(action, input), s)
    implies state_pred_call(kubernetes_api_next().pre(input), s) by {
        exists_next_kubernetes_api_step(action, input, s.kubernetes_api_state);
    };
}

pub proof fn controller_action_pre_implies_next_pre(action: ControllerAction, input: ControllerActionInput)
    requires
        controller().actions.contains(action),
    ensures
        valid(lift_state(controller_action_pre(action, input)).implies(lift_state(controller_next().pre(input)))),
{
    assert forall |s| #[trigger] state_pred_call(controller_action_pre(action, input), s)
    implies state_pred_call(controller_next().pre(input), s) by {
        exists_next_controller_step(action, input, s.controller_state);
    };
}

pub proof fn exists_next_kubernetes_api_step(action: KubernetesAPIAction, input: KubernetesAPIActionInput, s: kubernetes_api::State)
    requires
        kubernetes_api().actions.contains(action),
        (action.precondition)(input, s),
    ensures
        exists |step| (#[trigger] (kubernetes_api().step_to_action)(step).precondition)(input, s),
{
    assert(((kubernetes_api().step_to_action)(kubernetes_api::Step::HandleRequest).precondition)(input, s));
}

pub proof fn exists_next_controller_step(action: ControllerAction, input: ControllerActionInput, s: controller::State)
    requires
        controller().actions.contains(action),
        (action.precondition)(input, s),
    ensures
        exists |step| (#[trigger] (controller().step_to_action)(step).precondition)(input, s),
{
    if action === controller::trigger_reconcile() {
        let step = controller::Step::TriggerReconcile;
        assert(((controller().step_to_action)(step).precondition)(input, s));
    } else if action === controller::run_scheduled_reconcile() {
        let step = controller::Step::RunScheduledReconcile;
        assert(((controller().step_to_action)(step).precondition)(input, s));
    } else if action === controller::continue_reconcile() {
        let step = controller::Step::ContinueReconcile;
        assert(((controller().step_to_action)(step).precondition)(input, s));
    } else {
        let step = controller::Step::EndReconcile;
        assert(((controller().step_to_action)(step).precondition)(input, s));
    }
}

}
