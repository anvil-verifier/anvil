// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::spec::message::*;
use crate::reconciler::spec::reconciler::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub struct ControllerState<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> {
    pub ongoing_reconciles: Map<ObjectRef, OngoingReconcile<K, E, R>>,
    pub scheduled_reconciles: Map<ObjectRef, K>,
}

pub struct OngoingReconcile<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> {
    pub triggering_cr: K,
    // pending_req_msg: the request message pending for the handling for k8s api
    // pending_external_api_input: the request returned by the reconcile_core which should be sent to be external api
    pub pending_req_msg: Option<MsgType<E>>,
    pub local_state: R::T,
}

#[is_variant]
pub enum ControllerStep {
    RunScheduledReconcile,
    ContinueReconcile,
    EndReconcile,
}

pub struct ControllerActionInput<E: ExternalAPI> {
    pub recv: Option<MsgType<E>>,
    pub scheduled_cr_key: Option<ObjectRef>,
    pub rest_id_allocator: RestIdAllocator,
}

pub struct ControllerActionOutput<E: ExternalAPI> {
    pub send: Multiset<MsgType<E>>,
    pub rest_id_allocator: RestIdAllocator,
}

pub type ControllerStateMachine<K, E, R> = StateMachine<ControllerState<K, E, R>, ControllerActionInput<E>, ControllerActionInput<E>, ControllerActionOutput<E>, ControllerStep>;

pub type ControllerAction<K, E, R> = Action<ControllerState<K, E, R>, ControllerActionInput<E>, ControllerActionOutput<E>>;

}
