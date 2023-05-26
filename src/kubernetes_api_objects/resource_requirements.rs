// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct ResourceRequirements {
    inner: k8s_openapi::api::core::v1::ResourceRequirements
}

impl ResourceRequirements {
    #[verifier(external)]
    pub fn from_kube(inner: k8s_openapi::api::core::v1::ResourceRequirements) -> ResourceRequirements {
        ResourceRequirements { inner: inner }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> k8s_openapi::api::core::v1::ResourceRequirements {
        self.inner
    }
}

}
