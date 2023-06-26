// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::spec::message::*;
use crate::reconciler::spec::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use builtin::*;
use builtin_macros::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub struct ControllerState<K: ResourceView, T> {
    pub ongoing_reconciles: Map<ObjectRef, OngoingReconcile<K, T>>,
    pub scheduled_reconciles: Map<ObjectRef, K>,
}

pub struct OngoingReconcile<K: ResourceView, T> {
    pub triggering_cr: K,
    pub pending_req_msg: Option<Message>,
    pub local_state: T,
}

#[is_variant]
pub enum ControllerStep {
    RunScheduledReconcile,
    ContinueReconcile,
    EndReconcile,
}

pub struct ControllerActionInput {
    pub recv: Option<Message>,
    pub scheduled_cr_key: Option<ObjectRef>,
    pub rest_id_allocator: RestIdAllocator,
}

pub type ControllerActionOutput = (Multiset<Message>, RestIdAllocator);

pub type ControllerStateMachine<K, T> = StateMachine<ControllerState<K, T>, ControllerActionInput, ControllerActionInput, ControllerActionOutput, ControllerStep>;

pub type ControllerAction<K, T> = Action<ControllerState<K, T>, ControllerActionInput, ControllerActionOutput>;

pub open spec fn controller_req_msg(req: APIRequest, req_id: nat) -> Message {
    form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(req, req_id))
}

pub open spec fn init_controller_state<K: ResourceView, T>() -> ControllerState<K, T> {
    ControllerState {
        ongoing_reconciles: Map::empty(),
        scheduled_reconciles: Map::empty(),
    }
}

}
