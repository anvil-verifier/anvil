// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::spec::{common::*, resource::*};
use crate::kubernetes_cluster::spec::{
    api_server::types::{ApiServerAction, ApiServerActionInput, ApiServerState, ApiServerStep},
    builtin_controllers::types::*,
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerAction, ControllerActionInput, ControllerState, ControllerStep},
    external_api::types::{
        ExternalAPIAction, ExternalAPIActionInput, ExternalAPIState, ExternalAPIStep,
    },
    message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

impl <K: CustomResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub proof fn kubernetes_api_action_pre_implies_next_pre(action: ApiServerAction<E::Input, E::Output>, input: Option<MsgType<E>>)
    requires Self::kubernetes_api().actions.contains(action),
    ensures valid(lift_state(Self::kubernetes_api_action_pre(action, input)).implies(lift_state(Self::kubernetes_api_next().pre(input)))),
{
    assert forall |s: Self| #[trigger] Self::kubernetes_api_action_pre(action, input)(s)
    implies Self::kubernetes_api_next().pre(input)(s) by {
        Self::exists_next_kubernetes_api_step(
            action, ApiServerActionInput{recv: input}, s.kubernetes_api_state
        );
    };
}

pub proof fn exists_next_kubernetes_api_step(action: ApiServerAction<E::Input, E::Output>, input: ApiServerActionInput<E::Input, E::Output>, s: ApiServerState)
    requires
        Self::kubernetes_api().actions.contains(action),
        (action.precondition)(input, s),
    ensures exists |step| (#[trigger] (Self::kubernetes_api().step_to_action)(step).precondition)(input, s),
{
    assert(((Self::kubernetes_api().step_to_action)(ApiServerStep::HandleRequest).precondition)(input, s));
}

pub proof fn external_api_action_pre_implies_next_pre(action: ExternalAPIAction<E>, input: Option<MsgType<E>>)
    requires Self::external_api().actions.contains(action),
    ensures valid(lift_state(Self::external_api_action_pre(action, input)).implies(lift_state(Self::external_api_next().pre(input)))),
{
    assert forall |s: Self| #[trigger] Self::external_api_action_pre(action, input)(s)
    implies Self::external_api_next().pre(input)(s) by {
        Self::exists_next_external_api_step(
            action, ExternalAPIActionInput{recv: input, resources: s.kubernetes_api_state.resources}, s.external_api_state
        );
    };
}

pub proof fn exists_next_external_api_step(action: ExternalAPIAction<E>, input: ExternalAPIActionInput<E>, s: ExternalAPIState<E>)
    requires
        Self::external_api().actions.contains(action),
        (action.precondition)(input, s),
    ensures exists |step| (#[trigger] (Self::external_api().step_to_action)(step).precondition)(input, s),
{
    assert(((Self::external_api().step_to_action)(ExternalAPIStep::HandleExternalRequest).precondition)(input, s));
}

pub proof fn controller_action_pre_implies_next_pre(action: ControllerAction<K, E, R>, input: (Option<MsgType<E>>, Option<ObjectRef>))
    requires Self::controller().actions.contains(action),
    ensures valid(lift_state(Self::controller_action_pre(action, input)).implies(lift_state(Self::controller_next().pre(input)))),
{
    assert forall |s| #[trigger] Self::controller_action_pre(action, input)(s)
    implies Self::controller_next().pre(input)(s) by {
        Self::exists_next_controller_step(
            action,
            ControllerActionInput{recv: input.0, scheduled_cr_key: input.1, rest_id_allocator: s.rest_id_allocator},
            s.controller_state
        );
    };
}

pub proof fn exists_next_controller_step(action: ControllerAction<K, E, R>, input: ControllerActionInput<E>, s: ControllerState<K, E, R>)
    requires
        Self::controller().actions.contains(action),
        (action.precondition)(input, s),
    ensures exists |step| (#[trigger] (Self::controller().step_to_action)(step).precondition)(input, s),
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

pub proof fn builtin_controllers_action_pre_implies_next_pre(action: BuiltinControllersAction<E::Input, E::Output>, input: (BuiltinControllerChoice, ObjectRef))
    requires Self::builtin_controllers().actions.contains(action),
    ensures valid(lift_state(Self::builtin_controllers_action_pre(action, input)).implies(lift_state(Self::builtin_controllers_next().pre(input)))),
{
    assert forall |s: Self| #[trigger] Self::builtin_controllers_action_pre(action, input)(s)
    implies Self::builtin_controllers_next().pre(input)(s) by {
        Self::exists_next_builtin_controllers_step(
            action,
            BuiltinControllersActionInput{choice: input.0, key: input.1, rest_id_allocator: s.rest_id_allocator},
            s.kubernetes_api_state
        );
    };
}

pub proof fn exists_next_builtin_controllers_step(action: BuiltinControllersAction<E::Input, E::Output>, input: BuiltinControllersActionInput, s: ApiServerState)
    requires
        Self::builtin_controllers().actions.contains(action),
        (action.precondition)(input, s),
    ensures exists |step| (#[trigger] (Self::builtin_controllers().step_to_action)(step).precondition)(input, s),
{
    if action == Self::run_garbage_collector() {
        let step = BuiltinControllersStep::RunGarbageCollector;
        assert(((Self::builtin_controllers().step_to_action)(step).precondition)(input, s));
    } else if action == Self::run_stateful_set_controller() {
        let step = BuiltinControllersStep::RunStatefulSetController;
        assert(((Self::builtin_controllers().step_to_action)(step).precondition)(input, s));
    } else if action == Self::run_daemon_set_controller() {
        let step = BuiltinControllersStep::RunDaemonSetController;
        assert(((Self::builtin_controllers().step_to_action)(step).precondition)(input, s));
    } else {
        let step = BuiltinControllersStep::RunStabilizer;
        assert(((Self::builtin_controllers().step_to_action)(step).precondition)(input, s));
    }
}

}

}
