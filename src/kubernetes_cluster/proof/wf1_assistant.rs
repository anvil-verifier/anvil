// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{common::*, resource::*};
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
};
use crate::reconciler::spec::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;
use vstd::{option::*, seq::*, set::*};

verus! {

pub proof fn kubernetes_api_action_pre_implies_next_pre<K: ResourceView, T>(
    action: KubernetesAPIAction, input: Option<Message>
)
    requires
        kubernetes_api().actions.contains(action),
    ensures
        valid(
            lift_state(kubernetes_api_action_pre::<K, T>(action, input))
                .implies(lift_state(kubernetes_api_next().pre(input)))
        ),
{
    assert forall |s: State<K, T>| #[trigger] kubernetes_api_action_pre(action, input)(s)
    implies kubernetes_api_next().pre(input)(s) by {
        exists_next_kubernetes_api_step(
            action, KubernetesAPIActionInput{recv: input, chan_manager: s.chan_manager}, s.kubernetes_api_state
        );
    };
}

pub proof fn controller_action_pre_implies_next_pre<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    action: ControllerAction<K, T>, input: (Option<Message>, Option<ObjectRef>)
)
    requires
        controller::<K, T, ReconcilerType>().actions.contains(action),
    ensures
        valid(
            lift_state(controller_action_pre::<K, T, ReconcilerType>(action, input))
                .implies(lift_state(controller_next::<K, T, ReconcilerType>().pre(input)))
        ),
{
    assert forall |s| #[trigger] controller_action_pre::<K, T, ReconcilerType>(action, input)(s)
    implies controller_next::<K, T, ReconcilerType>().pre(input)(s) by {
        exists_next_controller_step::<K, T, ReconcilerType>(
            action,
            ControllerActionInput{recv: input.0, scheduled_cr_key: input.1, chan_manager: s.chan_manager},
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

pub proof fn exists_next_controller_step<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    action: ControllerAction<K, T>, input: ControllerActionInput, s: ControllerState<K, T>
)
    requires
        controller::<K, T, ReconcilerType>().actions.contains(action),
        (action.precondition)(input, s),
    ensures
        exists |step| (#[trigger] (controller::<K, T, ReconcilerType>().step_to_action)(step).precondition)(input, s),
{
    if action == run_scheduled_reconcile::<K, T, ReconcilerType>() {
        let step = ControllerStep::RunScheduledReconcile;
        assert(((controller::<K, T, ReconcilerType>().step_to_action)(step).precondition)(input, s));
    } else if action == continue_reconcile::<K, T, ReconcilerType>() {
        let step = ControllerStep::ContinueReconcile;
        assert(((controller::<K, T, ReconcilerType>().step_to_action)(step).precondition)(input, s));
    } else {
        let step = ControllerStep::EndReconcile;
        assert(((controller::<K, T, ReconcilerType>().step_to_action)(step).precondition)(input, s));
    }
}

}
