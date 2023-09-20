// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, error::ParseDynamicObjectError, marshal::*,
    object_meta::*, pod::*, resource::*,
};
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

#[verifier(external_body)]
pub struct PodTemplateSpec {
    inner: deps_hack::k8s_openapi::api::core::v1::PodTemplateSpec,
}

impl PodTemplateSpec {
    pub spec fn view(&self) -> PodTemplateSpecView;

    #[verifier(external_body)]
    pub fn default() -> (pod_template_spec: PodTemplateSpec)
        ensures
            pod_template_spec@ == PodTemplateSpecView::default(),
    {
        PodTemplateSpec {
            inner: deps_hack::k8s_openapi::api::core::v1::PodTemplateSpec::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_metadata(&mut self, metadata: ObjectMeta)
        ensures
            self@ == old(self)@.set_metadata(metadata@),
    {
        self.inner.metadata = Some(metadata.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: PodSpec)
        ensures
            self@ == old(self)@.set_spec(spec@),
    {
        self.inner.spec = Some(spec.into_kube());
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::PodTemplateSpec) -> PodTemplateSpec {
        PodTemplateSpec { inner: inner }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::PodTemplateSpec {
        self.inner
    }
}

pub struct PodTemplateSpecView {
    pub metadata: Option<ObjectMetaView>,
    pub spec: Option<PodSpecView>,
}

impl PodTemplateSpecView {
    pub open spec fn default() -> PodTemplateSpecView {
        PodTemplateSpecView {
            metadata: None,
            spec: None,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> PodTemplateSpecView {
        PodTemplateSpecView {
            metadata: Some(metadata),
            ..self
        }
    }

    pub open spec fn set_spec(self, spec: PodSpecView) -> PodTemplateSpecView {
        PodTemplateSpecView {
            spec: Some(spec),
            ..self
        }
    }
}

impl Marshalable for PodTemplateSpecView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

}
