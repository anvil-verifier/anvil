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
    pub fn kube_metadata_ref(&self) -> &deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta { &self.inner.metadata }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    // TODO: implement this function by parsing inner.types.unwrap().kind
    #[verifier(external_body)]
    pub fn kind(&self) -> (kind: Kind)
        ensures kind == self@.kind,
    {
        unimplemented!();
    }
}

impl ResourceWrapper<deps_hack::kube::api::DynamicObject> for DynamicObject {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::kube::api::DynamicObject) -> DynamicObject { DynamicObject { inner: inner } }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::kube::api::DynamicObject { self.inner }
}

impl std::clone::Clone for DynamicObject {
    #[verifier(external_body)]
    fn clone(&self) -> (result: Self)
        ensures result == self
    { DynamicObject { inner: self.inner.clone() } }
}

impl std::fmt::Debug for DynamicObject {
    #[verifier(external)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.inner.fmt(f) }
}

}
