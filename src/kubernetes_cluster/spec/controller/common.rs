// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::state_machine::action::*;
use crate::kubernetes_cluster::spec::{common::*, reconciler::*};
use crate::pervasive::{map::*, option::*, seq::*, set::*};
use crate::state_machine::state_machine::*;
use builtin::*;
use builtin_macros::*;

verus! {

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
