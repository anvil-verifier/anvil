// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::pod::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;
use vstd::vec::*;

verus! {

#[verifier(external_body)]
pub struct PodTemplateSpec {
    inner: k8s_openapi::api::core::v1::PodTemplateSpec,
}

impl PodTemplateSpec {
    pub spec fn view(&self) -> PodTemplateSpecView;

    #[verifier(external_body)]
    pub fn default() -> (pod_template_spec: PodTemplateSpec)
        ensures
            pod_template_spec@ == PodTemplateSpecView::default(),
    {
        PodTemplateSpec {
            inner: k8s_openapi::api::core::v1::PodTemplateSpec::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_metadata(&mut self, metadata: ObjectMeta)
        ensures
            self@ == old(self)@.set_metadata(metadata@),
    {
        self.inner.metadata = std::option::Option::Some(metadata.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: PodSpec)
        ensures
            self@ == old(self)@.set_spec(spec@),
    {
        self.inner.spec = std::option::Option::Some(spec.into_kube());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> k8s_openapi::api::core::v1::PodTemplateSpec {
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
            metadata: Option::None,
            spec: Option::None,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> PodTemplateSpecView {
        PodTemplateSpecView {
            metadata: Option::Some(metadata),
            ..self
        }
    }

    pub open spec fn set_spec(self, spec: PodSpecView) -> PodTemplateSpecView {
        PodTemplateSpecView {
            spec: Option::Some(spec),
            ..self
        }
    }

    pub open spec fn metadata_field() -> nat {0}

    pub open spec fn spec_field() -> nat {1}
}

impl Marshalable for PodTemplateSpecView {
    open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::metadata_field(), if self.metadata.is_None() { Value::Null } else {
                    self.metadata.get_Some_0().marshal()
                })
                .insert(Self::spec_field(), if self.spec.is_None() { Value::Null } else {
                    self.spec.get_Some_0().marshal()
                })
        )
    }

    open spec fn unmarshal(value: Value) -> Self {
        PodTemplateSpecView {
            metadata: if value.get_Object_0()[Self::metadata_field()].is_Null() { Option::None } else {
                Option::Some(ObjectMetaView::unmarshal(value.get_Object_0()[Self::metadata_field()]))
            },
            spec: if value.get_Object_0()[Self::spec_field()].is_Null() { Option::None } else {
                Option::Some(PodSpecView::unmarshal(value.get_Object_0()[Self::spec_field()]))
            },
        }
    }

    proof fn marshal_preserves_integrity() {
        PodSpecView::marshal_preserves_integrity();
    }
}

}
