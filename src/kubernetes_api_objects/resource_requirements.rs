// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::resource::*;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct ResourceRequirements {
    inner: deps_hack::k8s_openapi::api::core::v1::ResourceRequirements
}

impl ResourceRequirements {
    pub spec fn view(&self) -> ResourceRequirementsView;

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::ResourceRequirements) -> ResourceRequirements {
        ResourceRequirements { inner: inner }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ResourceRequirements {
        self.inner
    }
}

pub struct ResourceRequirementsView {}

impl ResourceRequirementsView {
    pub open spec fn default() -> ResourceRequirementsView {
        ResourceRequirementsView {}
    }
}

}
