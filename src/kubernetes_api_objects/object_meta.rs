// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {


/// ObjectMeta contains the metadata that all Kubernetes resource objects must have,
/// including name, namespace, uid, and so on.
///
/// This definition is a wrapper of ObjectMeta defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/apimachinery/pkg/apis/meta/v1/object_meta.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/reference/kubernetes-api/common-definitions/object-meta/.

#[verifier(external_body)]
pub struct ObjectMeta {
    inner: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta,
}

impl ObjectMeta {
    pub spec fn view(&self) -> ObjectMetaView;

    #[verifier(external_body)]
    pub fn default() -> (object_meta: ObjectMeta)
        ensures
            object_meta@ == ObjectMetaView::default(),
    {
        ObjectMeta {
            inner: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta::default(),
        }
    }

    #[verifier(external_body)]
    pub fn name(&self) -> (name: Option<String>)
        ensures
            self@.name.is_Some() == name.is_Some(),
            name.is_Some() ==> name.get_Some_0()@ == self@.name.get_Some_0(),
    {
        match &self.inner.name {
            std::option::Option::Some(n) => Option::Some(String::from_rust_string(n.to_string())),
            std::option::Option::None => Option::None,
        }
    }

    #[verifier(external_body)]
    pub fn namespace(&self) -> (namespace: Option<String>)
        ensures
            self@.namespace.is_Some() == namespace.is_Some(),
            namespace.is_Some() ==> namespace.get_Some_0()@ == self@.namespace.get_Some_0(),
    {
        match &self.inner.namespace {
            std::option::Option::Some(n) => Option::Some(String::from_rust_string(n.to_string())),
            std::option::Option::None => Option::None,
        }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = std::option::Option::Some(name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_namespace(&mut self, namespace: String)
        ensures
            self@ == old(self)@.set_namespace(namespace@),
    {
        self.inner.namespace = std::option::Option::Some(namespace.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_generate_name(&mut self, generate_name: String)
        ensures
            self@ == old(self)@.set_generate_name(generate_name@),
    {
        self.inner.generate_name = std::option::Option::Some(generate_name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_labels(&mut self, labels: StringMap)
        ensures
            self@ == old(self)@.set_labels(labels@),
    {
        self.inner.labels = std::option::Option::Some(labels.into_rust_map());
    }
}

impl ResourceWrapper<deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta> for ObjectMeta {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta) -> ObjectMeta {
        ObjectMeta { inner: inner }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
        self.inner
    }
}

/// ObjectMetaView is the ghost type of ObjectMeta.
/// It is supposed to be used in spec and proof code.

pub struct ObjectMetaView {
    pub name: Option<StringView>,
    pub namespace: Option<StringView>,
    pub generate_name: Option<StringView>,
    pub resource_version: Option<nat>, // make rv a nat so that it is easy to compare in spec/proof
    pub uid: Option<StringView>,
    pub labels: Option<Map<StringView, StringView>>,
}

impl ObjectMetaView {
    pub open spec fn default() -> ObjectMetaView {
        ObjectMetaView {
            name: Option::None,
            namespace: Option::None,
            generate_name: Option::None,
            resource_version: Option::None,
            uid: Option::None,
            labels: Option::None,
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ObjectMetaView {
        ObjectMetaView {
            name: Option::Some(name),
            ..self
        }
    }

    pub open spec fn set_namespace(self, namespace: StringView) -> ObjectMetaView {
        ObjectMetaView {
            namespace: Option::Some(namespace),
            ..self
        }
    }

    pub open spec fn set_generate_name(self, generate_name: StringView) -> ObjectMetaView {
        ObjectMetaView {
            generate_name: Option::Some(generate_name),
            ..self
        }
    }

    pub open spec fn set_labels(self, labels: Map<StringView, StringView>) -> ObjectMetaView {
        ObjectMetaView {
            labels: Option::Some(labels),
            ..self
        }
    }

    pub open spec fn set_resource_version(self, resource_version: nat) -> ObjectMetaView {
        ObjectMetaView {
            resource_version: Option::Some(resource_version),
            ..self
        }
    }

    pub open spec fn name_field() -> nat {0}

    pub open spec fn namespace_field() -> nat {1}

    pub open spec fn generate_name_field() -> nat {2}

    pub open spec fn resource_version_field() -> nat {3}

    pub open spec fn uid_field() -> nat {4}

    pub open spec fn labels_field() -> nat {5}
}

impl Marshalable for ObjectMetaView {
    closed spec fn marshal(self) -> Value;

    closed spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

}
