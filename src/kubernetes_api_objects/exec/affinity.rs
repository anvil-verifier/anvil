// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, object_meta::*, resource::*,
};
use crate::kubernetes_api_objects::spec::affinity::*;
use crate::vstd_ext::{string_map::*, string_view::*};
use vstd::prelude::*;

verus! {

/// Affinity is a group of affinity scheduling rules.
///
/// This definition is a wrapper of Affinity defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/affinity.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/scheduling-eviction/assign-pod-node/#affinity-and-anti-affinity.

#[verifier(external_body)]
pub struct Affinity {
    inner: deps_hack::k8s_openapi::api::core::v1::Affinity,
}

impl Affinity {
    pub spec fn view(&self) -> AffinityView;
}

#[verifier(external)]
impl ResourceWrapper<deps_hack::k8s_openapi::api::core::v1::Affinity> for Affinity {
    fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::Affinity) -> Affinity { Affinity { inner: inner } }

    fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Affinity { self.inner }
}

}
