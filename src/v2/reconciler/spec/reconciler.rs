// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{api_method::*, common::*, dynamic::*, resource::*};
use crate::kubernetes_cluster::spec::message::*;
use crate::reconciler::spec::io::*;
use vstd::prelude::*;

verus! {

// Reconciler is used to specify the custom controller as a state machine
// and install it to the Kubernetes cluster state machine.
pub trait Reconciler {
    // S: type of the reconciler state of the reconciler.
    type S;
    // K: type of the custom resource.
    type K: CustomResourceView;
    // EReq: type of request the controller sends to the external systems (if any).
    type EReq;
    // EResp: type of response the controller receives from the external systems (if any).
    type EResp;

    // reconcile_init_state returns the initial local state that the reconciler starts
    // its reconcile function with.
    spec fn reconcile_init_state() -> Self::S;

    // reconcile_core describes the logic of reconcile function and is the key logic we want to verify.
    // Each reconcile_core should take the local state and a response of the previous request (if any) as input
    // and outputs the next local state and the request to send to Kubernetes API (if any).
    spec fn reconcile_core(cr: Self::K, resp_o: Option<ResponseView<Self::EResp>>, state: Self::S) -> (Self::S, Option<RequestView<Self::EReq>>);

    // reconcile_done is used to tell the controller_runtime whether this reconcile round is done.
    // If it is true, controller_runtime will requeue the reconcile.
    spec fn reconcile_done(state: Self::S) -> bool;

    // reconcile_error is used to tell the controller_runtime whether this reconcile round returns with error.
    // If it is true, controller_runtime will requeue the reconcile with a shorter waiting time.
    spec fn reconcile_error(state: Self::S) -> bool;
}

}
