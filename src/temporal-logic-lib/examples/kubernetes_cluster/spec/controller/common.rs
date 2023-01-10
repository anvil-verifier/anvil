// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::kubernetes_cluster::spec::common::*;
use crate::pervasive::{map::*, option::*, seq::*, set::*};
use crate::state_machine::*;
use builtin::*;
use builtin_macros::*;

verus! {

// TODO: Make it a trait
// Different reconcilers should define different reconciler state
pub struct ReconcileState {
    pub reconcile_pc: nat,
    // nat is not the idea way of representing pc, but we cannot use enum here
    // because the enum type will be specific to the reconciler
}

pub type ReconcileInitState = FnSpec() -> ReconcileState;

pub type ReconcileCore = FnSpec(ResourceKey, Option<APIResponse>, ReconcileState) -> (ReconcileState, Option<APIRequest>);

pub type ReconcileTrigger = FnSpec(Message) -> Option<ResourceKey>;

pub type ReconcileDone = FnSpec(ReconcileState) -> bool;

pub struct Reconciler {
    pub reconcile_init_state: ReconcileInitState,
    pub reconcile_trigger: ReconcileTrigger,
    pub reconcile_core: ReconcileCore,
    pub reconcile_done: ReconcileDone,
}

pub struct OngoingReconcile {
    pub pending_req_msg: Option<Message>,
    pub local_state: ReconcileState,
}

pub struct ControllerState {
    pub ongoing_reconciles: Map<ResourceKey, OngoingReconcile>,
    pub scheduled_reconciles: Set<ResourceKey>,
}

pub struct ControllerActionInput {
    pub recv: Option<Message>,
    pub scheduled_cr_key: Option<ResourceKey>,
}

#[is_variant]
pub enum ControllerStep {
    TriggerReconcile,
    RunScheduledReconcile,
    ContinueReconcile,
    EndReconcile,
}

pub type ControllerStateMachine = StateMachine<ControllerState, ControllerActionInput, ControllerActionInput, Set<Message>, ControllerStep>;

pub type ControllerAction = Action<ControllerState, ControllerActionInput, Set<Message>>;

pub type ControllerActionResult = ActionResult<ControllerState, Set<Message>>;

pub open spec fn msg_to_kubernetes_api(msg_content: MessageContent) -> Message {
    form_msg(HostId::CustomController, HostId::KubernetesAPI, msg_content)
}

}
