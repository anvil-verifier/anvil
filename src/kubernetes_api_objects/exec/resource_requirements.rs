// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::spec::resource_requirements::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct ResourceRequirements {
    inner: deps_hack::k8s_openapi::api::core::v1::ResourceRequirements
}

impl ResourceRequirements {
    pub uninterp spec fn view(&self) -> ResourceRequirementsView;

    #[verifier(external_body)]
    pub fn default() -> (resource_requirements: ResourceRequirements)
        ensures resource_requirements@ == ResourceRequirementsView::default(),
    {
        ResourceRequirements {
            inner: deps_hack::k8s_openapi::api::core::v1::ResourceRequirements::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures s@ == self@,
    {
        ResourceRequirements { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_limits(&mut self, limits: StringMap)
        ensures self@ == old(self)@.with_limits(limits@),
    {
        self.inner.limits = Some(limits.into_rust_map().into_iter().map(|(k, v)| (k, deps_hack::k8s_openapi::apimachinery::pkg::api::resource::Quantity(v))).collect());
    }

    #[verifier(external_body)]
    pub fn set_requests(&mut self, requests: StringMap)
        ensures self@ == old(self)@.with_requests(requests@),
    {
        self.inner.requests = Some(requests.into_rust_map().into_iter().map(|(k, v)| (k, deps_hack::k8s_openapi::apimachinery::pkg::api::resource::Quantity(v))).collect());
    }
}

}

implement_resource_wrapper_trait!(
    ResourceRequirements,
    deps_hack::k8s_openapi::api::core::v1::ResourceRequirements
);
