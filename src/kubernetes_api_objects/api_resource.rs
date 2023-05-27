// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::object_meta::*;
use vstd::prelude::*;

use deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta as K8SObjectMeta;
use deps_hack::kube::api::ApiResource as K8SApiResource;

verus! {

/// ApiResource is used for creating API handles for DynamicObject.
///
/// This definition is a wrapper of ApiResource defined at
/// https://github.com/kube-rs/kube/blob/main/kube-core/src/discovery.rs.
/// It is supposed to be used in exec controller code.

#[verifier(external_body)]
pub struct ApiResource {
    inner: K8SApiResource,
}

impl ApiResource {
    pub spec fn view(&self) -> ApiResourceView;

    #[verifier(external)]
    pub fn from_kube(inner: K8SApiResource) -> ApiResource {
        ApiResource {
            inner: inner
        }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> K8SApiResource {
        self.inner
    }

    #[verifier(external)]
    pub fn as_kube_ref(&self) -> &K8SApiResource {
        &self.inner
    }
}

/// ApiResourceView is the ghost type of ApiResource.
/// It is supposed to be used in spec and proof code.

pub struct ApiResourceView {
    pub kind: Kind,
}

}
