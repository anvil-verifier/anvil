// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::spec::toleration::*;
use vstd::prelude::*;

verus! {

// The pod this Toleration is attached to tolerates any taint that matches
//
// This definition is a wrapper of Toleration defined at
// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/toleration.rs.
// It is supposed to be used in exec controller code.
//
// More detailed information: https://kubernetes.io/docs/concepts/scheduling-eviction/taint-and-toleration/.

#[verifier(external_body)]
pub struct Toleration {
    inner: deps_hack::k8s_openapi::api::core::v1::Toleration,
}

impl Toleration {
    pub uninterp spec fn view(&self) -> TolerationView;
}

}

implement_resource_wrapper_trait!(
    Toleration,
    deps_hack::k8s_openapi::api::core::v1::Toleration
);
