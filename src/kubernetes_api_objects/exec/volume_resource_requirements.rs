// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::spec::volume_resource_requirements::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;

verus! {

implement_field_wrapper_type!(
    VolumeResourceRequirements,
    k8s_openapi::api::core::v1::VolumeResourceRequirements,
    VolumeResourceRequirementsView
);

impl VolumeResourceRequirements {
    #[verifier(external_body)]
    pub fn set_limits(&mut self, limits: StringMap)
        ensures self@ == old(self)@.with_limits(limits@),
    {
        self.inner.limits = Some(limits.into_rust_map().into_iter().map(|(k, v)| (k, k8s_openapi::apimachinery::pkg::api::resource::Quantity(v))).collect());
    }

    #[verifier(external_body)]
    pub fn set_requests(&mut self, requests: StringMap)
        ensures self@ == old(self)@.with_requests(requests@),
    {
        self.inner.requests = Some(requests.into_rust_map().into_iter().map(|(k, v)| (k, k8s_openapi::apimachinery::pkg::api::resource::Quantity(v))).collect());
    }
}

}
