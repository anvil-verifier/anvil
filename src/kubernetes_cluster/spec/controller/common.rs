// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::spec::{common::*, reconciler::*};
use crate::pervasive::{map::*, multiset::*, option::*, seq::*, set::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct ControllerState<T> {
    pub req_id: nat,
    pub ongoing_reconciles: Map<ResourceKey, OngoingReconcile<T>>,
    pub scheduled_reconciles: Set<ResourceKey>,
    pub self_watcher: Watcher,
    // TODO: there should be watchers for `owns_with` and `watches_with`
}

pub struct OngoingReconcile<T> {
    pub pending_req_msg: Option<Message>,
    pub local_state: T,
}

pub struct Watcher {
    pub state: WatcherState,
    pub pending_req_msg: Option<Message>, // This should either the initial list or the watch
}

pub struct ControllerActionInput {
    pub recv: Option<Message>,
    pub scheduled_cr_key: Option<ResourceKey>,
}

#[is_variant]
pub enum WatcherState {
    Empty,
    InitListed,
    Watching,
}

#[is_variant]
pub enum ControllerStep {
    TriggerReconcile,
    RunScheduledReconcile,
    ContinueReconcile,
    EndReconcile,
}

pub type ControllerStateMachine<T> = StateMachine<ControllerState<T>, ControllerActionInput, ControllerActionInput, Multiset<Message>, ControllerStep>;

pub type ControllerAction<T> = Action<ControllerState<T>, ControllerActionInput, Multiset<Message>>;

pub type ControllerActionResult<T> = ActionResult<ControllerState<T>, Multiset<Message>>;

pub open spec fn controller_req_msg(req: APIRequest, req_id: nat) -> Message {
    form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(req, req_id))
}

}
