// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::{object_meta::*, resource::*};
use crate::kubernetes_api_objects::spec::dynamic::*;
use vstd::prelude::*;

verus! {

// DynamicObject is mainly used to pass requests/response between reconcile_core and the shim layer.
// We use DynamicObject in KubeAPIRequest and KubeAPIResponse so that they can carry the requests and responses
// for all kinds of Kubernetes resource objects without exhaustive pattern matching.

#[verifier(external_body)]
pub struct DynamicObject {
    inner: deps_hack::kube::api::DynamicObject,
}

implement_view_trait!(DynamicObject, DynamicObjectView);
implement_deep_view_trait!(DynamicObject, DynamicObjectView);
implement_clone_trait!(DynamicObject);

impl DynamicObject {
    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }
}

#[verifier(external)]
impl std::fmt::Debug for DynamicObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.inner.fmt(f) }
}

}

implement_resource_wrapper_trait!(DynamicObject, deps_hack::kube::api::DynamicObject);
