// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct ResourceRequirements {
    inner: deps_hack::k8s_openapi::api::core::v1::ResourceRequirements
}

impl ResourceRequirements {
    pub spec fn view(&self) -> ResourceRequirementsView;

    #[verifier(external_body)]
    pub fn default() -> (resource_requirements: ResourceRequirements)
        ensures
            resource_requirements@ == ResourceRequirementsView::default(),
    {
        ResourceRequirements {
            inner: deps_hack::k8s_openapi::api::core::v1::ResourceRequirements::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures
            s@ == self@,
    {
        ResourceRequirements { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_limits(&mut self, limits: StringMap)
        ensures
            self@ == old(self)@.set_limits(limits@),
    {
        self.inner.limits = Some(
            limits.into_rust_map()
                .into_iter()
                .map(|(k, v)| (k, deps_hack::k8s_openapi::apimachinery::pkg::api::resource::Quantity(v)))
                .collect()
        );
    }

    #[verifier(external_body)]
    pub fn set_requests(&mut self, requests: StringMap)
        ensures
            self@ == old(self)@.set_requests(requests@),
    {
        self.inner.requests = Some(
            requests.into_rust_map()
                .into_iter()
                .map(|(k, v)| (k, deps_hack::k8s_openapi::apimachinery::pkg::api::resource::Quantity(v)))
                .collect()
        );
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::ResourceRequirements) -> ResourceRequirements {
        ResourceRequirements { inner: inner }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ResourceRequirements {
        self.inner
    }
}

pub struct ResourceRequirementsView {
    pub limits: Option<Map<StringView, StringView>>,
    pub requests: Option<Map<StringView, StringView>>,
}

impl ResourceRequirementsView {
    pub open spec fn default() -> ResourceRequirementsView {
        ResourceRequirementsView {
            limits: None,
            requests: None,
        }
    }

    pub open spec fn set_limits(self, limits: Map<StringView, StringView>) -> ResourceRequirementsView {
        ResourceRequirementsView {
            limits: Some(limits),
            ..self
        }
    }

    pub open spec fn set_requests(self, requests: Map<StringView, StringView>) -> ResourceRequirementsView {
        ResourceRequirementsView {
            requests: Some(requests),
            ..self
        }
    }
}

}
