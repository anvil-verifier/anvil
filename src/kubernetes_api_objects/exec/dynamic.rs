// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::{object_meta::*, resource::*};
use crate::kubernetes_api_objects::spec::dynamic::*;
use crate::vstd_ext::option_lib::option_view;
use vstd::prelude::*;

verus! {

// DynamicObject is mainly used to pass requests/response between reconcile_core and the shim layer.
// We use DynamicObject in KubeAPIRequest and KubeAPIResponse so that they can carry the requests and responses
// for all kinds of Kubernetes resource objects without exhaustive pattern matching.

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

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }
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

implement_resource_wrapper_trait!(DynamicObject, deps_hack::kube::api::DynamicObject);
