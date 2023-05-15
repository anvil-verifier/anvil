// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::spec::message::*;
use builtin::*;
use builtin_macros::*;
use vstd::option::*;

verus! {

/// Reconciler is the key data structure we use to pack up all the custom controller-specific logic
/// and install it to the Kubernetes cluster state machine
pub struct Reconciler<#[verifier(maybe_negative)] K: ResourceView, #[verifier(maybe_negative)] T> {
    // reconcile_init_state returns the initial local state that the reconciler starts
    // its reconcile function with.
    // Currently the local state is hardcoded to a ReconcileState.
    // We would like to make ReconcileState more general and reconcile_init_state
    // can also be more flexible.
    pub reconcile_init_state: ReconcileInitState<T>,

    // reconcile_core describes the logic of reconcile function and is the key logic we want to verify.
    // Each reconcile_core should take the local state and a response of the previous request (if any) as input
    // and outputs the next local state and the request to send to Kubernetes API (if any).
    pub reconcile_core: ReconcileCore<T>,

    // reconcile_done is used to tell the controller_runtime whether this reconcile round is done.
    // If it is true, controller_runtime will probably requeue the reconcile.
    pub reconcile_done: ReconcileDone<T>,

    // reconcile_error is used to tell the controller_runtime whether this reconcile round returns with error.
    // If it is true, controller_runtime will requeue the reconcile.
    pub reconcile_error: ReconcileError<T>,

    // use K so that Rust no longer complains about "parameter `K` is never used"
    pub consume_kubernetes_resource_type: FnSpec(K) -> K,
}

pub type ReconcileInitState<T> = FnSpec() -> T;

pub type ReconcileTrigger = FnSpec(Message) -> Option<ObjectRef>;

pub type ReconcileCore<T> = FnSpec(ObjectRef, Option<APIResponse>, T) -> (T, Option<APIRequest>);

pub type ReconcileDone<T> = FnSpec(T) -> bool;

pub type ReconcileError<T> = FnSpec(T) -> bool;

}
