// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{api_method::*, common::*, dynamic::*, resource::*};
use crate::kubernetes_cluster::spec::message::*;
use crate::reconciler::spec::io::*;
use vstd::prelude::*;

verus! {

/// Reconciler is the key data structure we use to pack up all the custom controller-specific logic
/// and install it to the Kubernetes cluster state machine
#[verifier(reject_recursive_types(K))]
#[verifier(reject_recursive_types(ExternalAPIType))]
pub trait Reconciler<K: CustomResourceView, ExternalAPIType: ExternalAPI>: Sized {
    // Here are several internal associated types:
    // T: type of the reconciler state of the reconciler
    type T;

    // reconcile_init_state returns the initial local state that the reconciler starts
    // its reconcile function with.
    // Currently the local state is hardcoded to a ReconcileState.
    // We would like to make ReconcileState more general and reconcile_init_state
    // can also be more flexible.
    spec fn reconcile_init_state() -> Self::T;

    // reconcile_core describes the logic of reconcile function and is the key logic we want to verify.
    // Each reconcile_core should take the local state and a response of the previous request (if any) as input
    // and outputs the next local state and the request to send to Kubernetes API (if any).
    spec fn reconcile_core(cr: K, resp_o: Option<ResponseView<ExternalAPIType::Output>>, state: Self::T)
        -> (Self::T, Option<RequestView<ExternalAPIType::Input>>);

    // reconcile_done is used to tell the controller_runtime whether this reconcile round is done.
    // If it is true, controller_runtime will probably requeue the reconcile.
    spec fn reconcile_done(state: Self::T) -> bool;

    // reconcile_error is used to tell the controller_runtime whether this reconcile round returns with error.
    // If it is true, controller_runtime will requeue the reconcile.
    spec fn reconcile_error(state: Self::T) -> bool;

    // expect_from_user describes the objects (besides the cr object) that the controller expect to be created by the user,
    // such as a secret object for storing credentials.
    spec fn expect_from_user(obj: DynamicObjectView) -> bool;
}

}
