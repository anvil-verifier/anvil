// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::spec::message::*;
use crate::reconciler::spec::reconciler::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub struct ControllerState<K: ResourceView, R: Reconciler<K>> {
    pub ongoing_reconciles: Map<ObjectRef, OngoingReconcile<K, R>>,
    pub scheduled_reconciles: Map<ObjectRef, K>,
    pub external_lib_state: R::LibState,
}

pub struct OngoingReconcile<K: ResourceView, R: Reconciler<K>> {
    pub triggering_cr: K,
    // pending_req_msg: the request message pending for the handling for k8s api
    // lib_response: the response returned by the external library if a request has been processed by it
    pub pending_req_msg: Option<Message>,
    pub lib_response: Option<R::LibResponse>,
    pub local_state: R::T,
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

pub type ControllerStateMachine<K, R> = StateMachine<ControllerState<K, R>, ControllerActionInput, ControllerActionInput, ControllerActionOutput, ControllerStep>;

pub type ControllerAction<K, R> = Action<ControllerState<K, R>, ControllerActionInput, ControllerActionOutput>;

pub open spec fn controller_req_msg(req: APIRequest, req_id: nat) -> Message {
    form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(req, req_id))
}

pub open spec fn init_controller_state<K: ResourceView, R: Reconciler<K>>() -> ControllerState<K, R> {
    ControllerState {
        ongoing_reconciles: Map::empty(),
        scheduled_reconciles: Map::empty(),
        external_lib_state: R::library_init_state(),
    }
}

}
