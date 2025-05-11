// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::spec::affinity::*;
use vstd::prelude::*;

verus! {

// Affinity is a group of affinity scheduling rules.
//
// This definition is a wrapper of Affinity defined at
// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/affinity.rs.
// It is supposed to be used in exec controller code.
//
// More detailed information: https://kubernetes.io/docs/concepts/scheduling-eviction/assign-pod-node/#affinity-and-anti-affinity.

#[verifier(external_body)]
pub struct Affinity {
    inner: deps_hack::k8s_openapi::api::core::v1::Affinity,
}

impl Affinity {
    pub spec fn view(&self) -> AffinityView;
}

}

implement_resource_wrapper!(Affinity, deps_hack::k8s_openapi::api::core::v1::Affinity);
