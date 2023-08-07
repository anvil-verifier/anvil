// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::owner_reference::*;
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
            Some(n) => Some(String::from_rust_string(n.to_string())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn namespace(&self) -> (namespace: Option<String>)
        ensures
            self@.namespace.is_Some() == namespace.is_Some(),
            namespace.is_Some() ==> namespace.get_Some_0()@ == self@.namespace.get_Some_0(),
    {
        match &self.inner.namespace {
            Some(n) => Some(String::from_rust_string(n.to_string())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn resource_version(&self) -> (version: Option<u64>)
        ensures
            self@.resource_version.is_Some() == version.is_Some(),
            version.is_Some() ==> version.get_Some_0() == self@.resource_version.get_Some_0(),
    {
        match &self.inner.resource_version {
            Some(n) => Some( n.parse::<std::primitive::u64>().unwrap() as u64 ),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = Some(name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_namespace(&mut self, namespace: String)
        ensures
            self@ == old(self)@.set_namespace(namespace@),
    {
        self.inner.namespace = Some(namespace.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_generate_name(&mut self, generate_name: String)
        ensures
            self@ == old(self)@.set_generate_name(generate_name@),
    {
        self.inner.generate_name = Some(generate_name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_labels(&mut self, labels: StringMap)
        ensures
            self@ == old(self)@.set_labels(labels@),
    {
        self.inner.labels = Some(labels.into_rust_map());
    }

    #[verifier(external_body)]
    pub fn set_annotations(&mut self, annotations: StringMap)
        ensures
            self@ == old(self)@.set_annotations(annotations@),
    {
        self.inner.annotations = Some(annotations.into_rust_map());
    }

    #[verifier(external_body)]
    pub fn set_owner_references(&mut self, owner_references: Vec<OwnerReference>)
        ensures
            self@ == old(self)@.set_owner_references(owner_references@.map_values(|o: OwnerReference| o@)),
    {
        self.inner.owner_references = Some(
            owner_references.into_iter().map(|o: OwnerReference| o.into_kube()).collect(),
        );
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
    pub uid: Option<nat>,
    pub labels: Option<Map<StringView, StringView>>,
    pub annotations: Option<Map<StringView, StringView>>,
    pub owner_references: Option<Seq<OwnerReferenceView>>,
}

impl ObjectMetaView {
    pub open spec fn default() -> ObjectMetaView {
        ObjectMetaView {
            name: None,
            namespace: None,
            generate_name: None,
            resource_version: None,
            uid: None,
            labels: None,
            annotations: None,
            owner_references: None,
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ObjectMetaView {
        ObjectMetaView {
            name: Some(name),
            ..self
        }
    }

    pub open spec fn set_namespace(self, namespace: StringView) -> ObjectMetaView {
        ObjectMetaView {
            namespace: Some(namespace),
            ..self
        }
    }

    pub open spec fn set_generate_name(self, generate_name: StringView) -> ObjectMetaView {
        ObjectMetaView {
            generate_name: Some(generate_name),
            ..self
        }
    }

    pub open spec fn set_labels(self, labels: Map<StringView, StringView>) -> ObjectMetaView {
        ObjectMetaView {
            labels: Some(labels),
            ..self
        }
    }

    pub open spec fn set_annotations(self, annotations: Map<StringView, StringView>) -> ObjectMetaView {
        ObjectMetaView {
            annotations: Some(annotations),
            ..self
        }
    }

    pub open spec fn set_resource_version(self, resource_version: nat) -> ObjectMetaView {
        ObjectMetaView {
            resource_version: Some(resource_version),
            ..self
        }
    }

    pub open spec fn set_owner_references(self, owner_references: Seq<OwnerReferenceView>) -> ObjectMetaView {
        ObjectMetaView {
            owner_references: Some(owner_references),
            ..self
        }
    }
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
