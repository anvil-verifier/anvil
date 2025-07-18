// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::{object_meta::*, pod::*, resource::*};
use crate::kubernetes_api_objects::spec::pod_template_spec::*;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct PodTemplateSpec {
    inner: deps_hack::k8s_openapi::api::core::v1::PodTemplateSpec,
}

impl PodTemplateSpec {
    pub uninterp spec fn view(&self) -> PodTemplateSpecView;

    #[verifier(external_body)]
    pub fn eq(&self, other: &Self) -> (b: bool)
        ensures b == (self.view() == other.view())
    {
        self.inner == other.inner
    }

    #[verifier(external_body)]
    pub fn default() -> (pod_template_spec: PodTemplateSpec)
        ensures pod_template_spec@ == PodTemplateSpecView::default(),
    {
        PodTemplateSpec {
            inner: deps_hack::k8s_openapi::api::core::v1::PodTemplateSpec::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (pod_template_spec: PodTemplateSpec)
        ensures pod_template_spec@ == self@,
    {
        PodTemplateSpec { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: Option<ObjectMeta>)
        ensures
            self@.metadata is Some == metadata is Some,
            metadata is Some ==> metadata->0@ == self@.metadata->0,
    {
        match &self.inner.metadata {
            Some(m) => Some(ObjectMeta::from_kube(m.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: Option<PodSpec>)
        ensures
            self@.spec is Some == spec is Some,
            spec is Some ==> spec->0@ == self@.spec->0,
    {
        match &self.inner.spec {
            Some(s) => Some(PodSpec::from_kube(s.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn set_metadata(&mut self, metadata: ObjectMeta)
        ensures self@ == old(self)@.with_metadata(metadata@),
    {
        self.inner.metadata = Some(metadata.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: PodSpec)
        ensures self@ == old(self)@.with_spec(spec@),
    {
        self.inner.spec = Some(spec.into_kube());
    }
}

}

implement_resource_wrapper_trait!(
    PodTemplateSpec,
    deps_hack::k8s_openapi::api::core::v1::PodTemplateSpec
);
