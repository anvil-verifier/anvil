// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{object_meta::*, owner_reference::*, resource::*};
use crate::kubernetes_api_objects::spec::{common::*, dynamic::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

/// DynamicObject is mainly used to pass requests/response between reconcile_core and the shim layer.
/// We use DynamicObject in KubeAPIRequest and KubeAPIResponse so that they can carry the requests and responses
/// for all kinds of Kubernetes resource objects without exhaustive pattern matching.

#[verifier(external_body)]
pub struct DynamicObject {
    inner: deps_hack::kube::api::DynamicObject,
}

impl View for DynamicObject {
    type V = DynamicObjectView;

    spec fn view(&self) -> DynamicObjectView;
}

impl DynamicObject {
    #[verifier(external)]
    pub fn kube_metadata_ref(&self) -> &deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
        &self.inner.metadata
    }

    #[verifier(external)]
    pub fn as_kube_ref(&self) -> &deps_hack::kube::api::DynamicObject {
        &self.inner
    }

    #[verifier(external)]
    pub fn as_kube_mut_ref(&mut self) -> &mut deps_hack::kube::api::DynamicObject {
        &mut self.inner
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }
}

#[verifier(external)]
impl ResourceWrapper<deps_hack::kube::api::DynamicObject> for DynamicObject {
    fn from_kube(inner: deps_hack::kube::api::DynamicObject) -> DynamicObject { DynamicObject { inner: inner } }

    fn into_kube(self) -> deps_hack::kube::api::DynamicObject { self.inner }
}

impl std::clone::Clone for DynamicObject {
    #[verifier(external_body)]
    fn clone(&self) -> (result: Self)
        ensures result == self
    { DynamicObject { inner: self.inner.clone() } }
}

#[verifier(external)]
impl std::fmt::Debug for DynamicObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.inner.fmt(f) }
}

}
