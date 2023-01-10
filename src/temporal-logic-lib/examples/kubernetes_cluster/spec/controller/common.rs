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

/// let's start from simple and forget about CreateStsDone for now
pub enum ReconcileCoreStep {
    Init,
    GetCRDone,
    CreateCMDone,
    // CreateStsDone,
    Done,
    Error
}

pub open spec fn ending_step(step: ReconcileCoreStep) -> bool {
    ||| step === ReconcileCoreStep::Done
    ||| step === ReconcileCoreStep::Error
}

pub struct ReconcileState {
    pub reconcile_step: ReconcileCoreStep,
    pub pending_req_msg: Option<Message>,
}

pub struct ControllerState {
    pub ongoing_reconciles: Map<ResourceKey, ReconcileState>,
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
