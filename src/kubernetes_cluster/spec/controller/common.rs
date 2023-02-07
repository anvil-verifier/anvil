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

pub struct OngoingReconcile<RS> {
    pub pending_req_msg: Option<Message>,
    pub local_state: RS,
}

pub struct ControllerState<RS> {
    pub ongoing_reconciles: Map<ResourceKey, OngoingReconcile<RS>>,
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

pub type ControllerStateMachine<RS> = StateMachine<ControllerState<RS>, ControllerActionInput, ControllerActionInput, Set<Message>, ControllerStep>;

pub type ControllerAction<RS> = Action<ControllerState<RS>, ControllerActionInput, Set<Message>>;

pub type ControllerActionResult<RS> = ActionResult<ControllerState<RS>, Set<Message>>;

pub open spec fn controller_req_msg(req: APIRequest) -> Message {
    form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(req))
}

}
