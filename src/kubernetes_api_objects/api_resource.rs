// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::object_meta::*;
use vstd::prelude::*;

use k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta as K8SObjectMeta;
use kube::api::ApiResource as K8SApiResource;

verus! {

#[verifier(external_body)]
pub struct ApiResource {
    inner: K8SApiResource,
}

pub struct ApiResourceView {
    pub kind: Kind,
}

impl ApiResource {
    pub spec fn view(&self) -> ApiResourceView;

    #[verifier(external)]
    pub fn from_kube_api_resource(inner: K8SApiResource) -> ApiResource {
        ApiResource {
            inner: inner
        }
    }

    #[verifier(external)]
    pub fn into_kube_api_resource(self) -> K8SApiResource {
        self.inner
    }

    #[verifier(external)]
    pub fn as_kube_api_resource_ref(&self) -> &K8SApiResource {
        &self.inner
    }
}

}
