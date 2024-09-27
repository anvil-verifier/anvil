// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::kubernetes_cluster::spec::message::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub struct ControllerState {
    pub ongoing_reconciles: Map<ObjectRef, OngoingReconcile>,
    pub scheduled_reconciles: Map<ObjectRef, DynamicObjectView>,
}

pub type ReconcileLocalState = Value;

pub enum RequestContent {
    KubernetesRequest(APIRequest),
    ExternalRequest(ExternalRequest),
}

pub enum ResponseContent {
    KubernetesResponse(APIResponse),
    ExternalResponse(ExternalResponse),
}

pub struct ReconcileModel {
    pub kind: Kind,
    pub init: spec_fn() -> ReconcileLocalState,
    pub transition: spec_fn(DynamicObjectView, Option<ResponseContent>, ReconcileLocalState) -> (ReconcileLocalState, Option<RequestContent>),
    pub done: spec_fn(ReconcileLocalState) -> bool,
    pub error: spec_fn(ReconcileLocalState) -> bool,
}

pub struct OngoingReconcile {
    pub triggering_cr: DynamicObjectView,
    pub pending_req_msg: Option<Message>,
    pub local_state: ReconcileLocalState,
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
    pub rpc_id_allocator: RPCIdAllocator,
}

pub struct ControllerActionOutput {
    pub send: Multiset<Message>,
    pub rpc_id_allocator: RPCIdAllocator,
}

pub type ControllerStateMachine = StateMachine<ControllerState, ControllerActionInput, ControllerActionInput, ControllerActionOutput, ControllerStep>;

pub type ControllerAction = Action<ControllerState, ControllerActionInput, ControllerActionOutput>;

}
