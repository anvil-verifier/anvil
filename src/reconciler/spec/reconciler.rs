// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::spec::message::*;
use crate::reconciler::spec::io::*;
use vstd::prelude::*;

verus! {

/// Reconciler is the key data structure we use to pack up all the custom controller-specific logic
/// and install it to the Kubernetes cluster state machine
pub trait Reconciler<#[verifier(maybe_negative)] K: ResourceView>: Sized {
    // Here are several internal associated types:
    // T: type of the reconciler state of the reconciler
    // I: type of the request (input) to the external library
    // O: type of the response (output) from the external library
    // S: type of the state of the external library
    type T;
    type I;
    type O;
    type S;

    // reconcile_init_state returns the initial local state that the reconciler starts
    // its reconcile function with.
    // Currently the local state is hardcoded to a ReconcileState.
    // We would like to make ReconcileState more general and reconcile_init_state
    // can also be more flexible.
    open spec fn reconcile_init_state() -> Self::T;

    // reconcile_core describes the logic of reconcile function and is the key logic we want to verify.
    // Each reconcile_core should take the local state and a response of the previous request (if any) as input
    // and outputs the next local state and the request to send to Kubernetes API (if any).
    open spec fn reconcile_core(cr: K, resp_o: Option<ResponseView<Self::O>>, state: Self::T)
        -> (Self::T, Option<RequestView<Self::I>>);

    // reconcile_done is used to tell the controller_runtime whether this reconcile round is done.
    // If it is true, controller_runtime will probably requeue the reconcile.
    open spec fn reconcile_done(state: Self::T) -> bool;

    // reconcile_error is used to tell the controller_runtime whether this reconcile round returns with error.
    // If it is true, controller_runtime will requeue the reconcile.
    open spec fn reconcile_error(state: Self::T) -> bool;

    // external_process describes the logic of external libraries, which is a spec counterpart of Lib::process.
    // An alternative way to achieve this is add Lib as a generic or associated type to this Reconciler trait. But since 
    // Lib should contain method process, it should implement a trait (which should be the spec version of ExternalLibrary).
    // It must be a generic currently. This will cause another round of super annoying refactoring. So currently we just
    // add another method to this trait.
    // This method consumes the input (which should be computed by reconcile_core) and the current state of the external
    // library and produces the response and the next state of the library.
    // Use optional state here because: (1) it's easy to initialize since we don't have to require a default or init method,
    // (2) some libraries don't need a state to hold information, thus, optional state makes sense. 
    open spec fn external_process(input: Self::I, state: Option<Self::S>) -> (Option<Self::O>, Option<Self::S>);
}

}
