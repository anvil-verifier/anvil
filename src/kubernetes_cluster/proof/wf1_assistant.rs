// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_cluster::spec::{
    controller,
    controller::common::{
        ControllerAction, ControllerActionInput, ControllerState, ControllerStep,
    },
    controller::controller_runtime::{continue_reconcile, end_reconcile, run_scheduled_reconcile},
    controller::state_machine::controller,
    distributed_system::*,
    kubernetes_api::common::{
        KubernetesAPIAction, KubernetesAPIActionInput, KubernetesAPIState, KubernetesAPIStep,
    },
    kubernetes_api::state_machine::kubernetes_api,
    message::*,
    reconciler::Reconciler,
};
use crate::pervasive::{option::*, seq::*, set::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn kubernetes_api_action_pre_implies_next_pre<T>(action: KubernetesAPIAction, input: Option<Message>)
    requires
        kubernetes_api().actions.contains(action),
    ensures
        valid(lift_state(kubernetes_api_action_pre::<T>(action, input)).implies(lift_state(kubernetes_api_next().pre(input)))),
{
    assert forall |s: State<T>| #[trigger] kubernetes_api_action_pre(action, input)(s) implies kubernetes_api_next().pre(input)(s) by {
        exists_next_kubernetes_api_step(action, (input, s.channel_manager), s.kubernetes_api_state);
    };
}

pub proof fn controller_action_pre_implies_next_pre<T>(reconciler: Reconciler<T>, action: ControllerAction<T>, input: (Option<Message>, Option<ObjectRef>))
    requires
        controller(reconciler).actions.contains(action),
    ensures
        valid(lift_state(controller_action_pre(reconciler, action, input)).implies(lift_state(controller_next(reconciler).pre(input)))),
{
    assert forall |s| #[trigger] controller_action_pre(reconciler, action, input)(s) implies controller_next(reconciler).pre(input)(s) by {
        exists_next_controller_step(reconciler, action, (input.0, input.1, s.channel_manager), s.controller_state);
    };
}

pub proof fn exists_next_kubernetes_api_step(action: KubernetesAPIAction, input: KubernetesAPIActionInput, s: KubernetesAPIState)
    requires
        kubernetes_api().actions.contains(action),
        (action.precondition)(input, s),
    ensures
        exists |step| (#[trigger] (kubernetes_api().step_to_action)(step).precondition)(input, s),
{
    assert(((kubernetes_api().step_to_action)(KubernetesAPIStep::HandleRequest).precondition)(input, s));
}

pub proof fn exists_next_controller_step<T>(reconciler: Reconciler<T>, action: ControllerAction<T>, input: ControllerActionInput, s: ControllerState<T>)
    requires
        controller(reconciler).actions.contains(action),
        (action.precondition)(input, s),
    ensures
        exists |step| (#[trigger] (controller(reconciler).step_to_action)(step).precondition)(input, s),
{
    if action == run_scheduled_reconcile(reconciler) {
        let step = ControllerStep::RunScheduledReconcile;
        assert(((controller(reconciler).step_to_action)(step).precondition)(input, s));
    } else if action == continue_reconcile(reconciler) {
        let step = ControllerStep::ContinueReconcile;
        assert(((controller(reconciler).step_to_action)(step).precondition)(input, s));
    } else {
        let step = ControllerStep::EndReconcile;
        assert(((controller(reconciler).step_to_action)(step).precondition)(input, s));
    }
}

}
