// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{common::*, resource::*};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller,
    controller::common::{
        ControllerAction, ControllerActionInput, ControllerState, ControllerStep,
    },
    controller::controller_runtime::{continue_reconcile, end_reconcile, run_scheduled_reconcile},
    controller::state_machine::controller,
    kubernetes_api::common::{
        KubernetesAPIAction, KubernetesAPIActionInput, KubernetesAPIState, KubernetesAPIStep,
    },
    kubernetes_api::state_machine::kubernetes_api,
    message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub proof fn kubernetes_api_action_pre_implies_next_pre<K: ResourceView, R: Reconciler<K>>(
    action: KubernetesAPIAction, input: Option<Message>
)
    requires
        kubernetes_api().actions.contains(action),
    ensures
        valid(
            lift_state(kubernetes_api_action_pre::<K, R>(action, input))
                .implies(lift_state(kubernetes_api_next().pre(input)))
        ),
{
    assert forall |s: State<K, R>| #[trigger] kubernetes_api_action_pre(action, input)(s)
    implies kubernetes_api_next().pre(input)(s) by {
        exists_next_kubernetes_api_step(
            action, KubernetesAPIActionInput{recv: input, rest_id_allocator: s.rest_id_allocator}, s.kubernetes_api_state
        );
    };
}

pub proof fn controller_action_pre_implies_next_pre<K: ResourceView, R: Reconciler<K>>(
    action: ControllerAction<K, R>, input: (Option<Message>, Option<ObjectRef>)
)
    requires
        controller::<K, R>().actions.contains(action),
    ensures
        valid(
            lift_state(controller_action_pre::<K, R>(action, input))
                .implies(lift_state(controller_next::<K, R>().pre(input)))
        ),
{
    assert forall |s| #[trigger] controller_action_pre::<K, R>(action, input)(s)
    implies controller_next::<K, R>().pre(input)(s) by {
        exists_next_controller_step::<K, R>(
            action,
            ControllerActionInput{recv: input.0, scheduled_cr_key: input.1, rest_id_allocator: s.rest_id_allocator},
            s.controller_state
        );
    };
}

pub proof fn exists_next_kubernetes_api_step(
    action: KubernetesAPIAction, input: KubernetesAPIActionInput, s: KubernetesAPIState
)
    requires
        kubernetes_api().actions.contains(action),
        (action.precondition)(input, s),
    ensures
        exists |step| (#[trigger] (kubernetes_api().step_to_action)(step).precondition)(input, s),
{
    assert(((kubernetes_api().step_to_action)(KubernetesAPIStep::HandleRequest).precondition)(input, s));
}

pub proof fn exists_next_controller_step<K: ResourceView, R: Reconciler<K>>(
    action: ControllerAction<K, R>, input: ControllerActionInput, s: ControllerState<K, R>
)
    requires
        controller::<K, R>().actions.contains(action),
        (action.precondition)(input, s),
    ensures
        exists |step| (#[trigger] (controller::<K, R>().step_to_action)(step).precondition)(input, s),
{
    if action == run_scheduled_reconcile::<K, R>() {
        let step = ControllerStep::RunScheduledReconcile;
        assert(((controller::<K, R>().step_to_action)(step).precondition)(input, s));
    } else if action == continue_reconcile::<K, R>() {
        let step = ControllerStep::ContinueReconcile;
        assert(((controller::<K, R>().step_to_action)(step).precondition)(input, s));
    } else {
        let step = ControllerStep::EndReconcile;
        assert(((controller::<K, R>().step_to_action)(step).precondition)(input, s));
    }
}

}
