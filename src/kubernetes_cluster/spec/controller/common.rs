// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::spec::{common::*, reconciler::*};
use crate::pervasive::{map::*, option::*, seq::*, set::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct OngoingReconcile<T> {
    pub pending_req_msg: Option<Message>,
    pub local_state: T,
}

pub struct ControllerState<T> {
    pub ongoing_reconciles: Map<ResourceKey, OngoingReconcile<T>>,
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

pub type ControllerStateMachine<T> = StateMachine<ControllerState<T>, ControllerActionInput, ControllerActionInput, Set<Message>, ControllerStep>;

pub type ControllerAction<T> = Action<ControllerState<T>, ControllerActionInput, Set<Message>>;

pub type ControllerActionResult<T> = ActionResult<ControllerState<T>, Set<Message>>;

pub open spec fn controller_req_msg(req: APIRequest) -> Message {
    form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(req))
}

}
