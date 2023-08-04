// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::{common::*, resource::*};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller,
    controller::common::{
        ControllerAction, ControllerActionInput, ControllerState, ControllerStep,
    },
    controller::state_machine::*,
    external_api::*,
    kubernetes_api::common::{
        KubernetesAPIAction, KubernetesAPIActionInput, KubernetesAPIState, KubernetesAPIStep,
    },
    kubernetes_api::state_machine::*,
    message::*,
};
use crate::kubernetes_cluster::Cluster;
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub proof fn kubernetes_api_action_pre_implies_next_pre(
    action: KubernetesAPIAction, input: Option<Message>
)
    requires
        Self::kubernetes_api().actions.contains(action),
    ensures
        valid(
            lift_state(Self::kubernetes_api_action_pre(action, input))
                .implies(lift_state(Self::kubernetes_api_next().pre(input)))
        ),
{
    assert forall |s: State<K, E, R>| #[trigger] Self::kubernetes_api_action_pre(action, input)(s)
    implies Self::kubernetes_api_next().pre(input)(s) by {
        Self::exists_next_kubernetes_api_step(
            action, KubernetesAPIActionInput{recv: input, rest_id_allocator: s.rest_id_allocator}, s.kubernetes_api_state
        );
    };
}

pub proof fn controller_action_pre_implies_next_pre(
    action: ControllerAction<K, E, R>, input: (Option<Message>, Option<ExternalComm<E::Input, E::Output>>, Option<ObjectRef>)
)
    requires
        Self::controller().actions.contains(action),
    ensures
        valid(
            lift_state(Self::controller_action_pre(action, input))
                .implies(lift_state(Self::controller_next().pre(input)))
        ),
{
    assert forall |s| #[trigger] Self::controller_action_pre(action, input)(s)
    implies Self::controller_next().pre(input)(s) by {
        Self::exists_next_controller_step(
            action,
            ControllerActionInput{recv: input.0, external_api_output: input.1, scheduled_cr_key: input.2, rest_id_allocator: s.rest_id_allocator},
            s.controller_state
        );
    };
}

pub proof fn exists_next_kubernetes_api_step(
    action: KubernetesAPIAction, input: KubernetesAPIActionInput, s: KubernetesAPIState
)
    requires
        Self::kubernetes_api().actions.contains(action),
        (action.precondition)(input, s),
    ensures
        exists |step| (#[trigger] (Self::kubernetes_api().step_to_action)(step).precondition)(input, s),
{
    assert(((Self::kubernetes_api().step_to_action)(KubernetesAPIStep::HandleRequest).precondition)(input, s));
}

pub proof fn exists_next_controller_step(
    action: ControllerAction<K, E, R>, input: ControllerActionInput<E>, s: ControllerState<K, E, R>
)
    requires
        Self::controller().actions.contains(action),
        (action.precondition)(input, s),
    ensures
        exists |step| (#[trigger] (Self::controller().step_to_action)(step).precondition)(input, s),
{
    if action == Self::run_scheduled_reconcile() {
        let step = ControllerStep::RunScheduledReconcile;
        assert(((Self::controller().step_to_action)(step).precondition)(input, s));
    } else if action == Self::continue_reconcile() {
        let step = ControllerStep::ContinueReconcile;
        assert(((Self::controller().step_to_action)(step).precondition)(input, s));
    } else {
        let step = ControllerStep::EndReconcile;
        assert(((Self::controller().step_to_action)(step).precondition)(input, s));
    }
}

}

}
