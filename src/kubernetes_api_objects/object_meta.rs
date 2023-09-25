// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    common::*, error::ParseDynamicObjectError, marshal::*, owner_reference::*, resource::*,
};
use crate::vstd_ext::string_map::*;
use crate::vstd_ext::string_view::*;
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
    pub fn clone(&self) -> (s: Self)
        ensures
            s@ == self@,
    {
        ObjectMeta { inner: self.inner.clone() }
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
    pub fn labels(&self) -> (labels: Option<StringMap>)
        ensures
            self@.labels.is_Some() == labels.is_Some(),
            labels.is_Some() ==> labels.get_Some_0()@ == self@.labels.get_Some_0(),
    {
        match &self.inner.labels {
            Some(l) => Some(StringMap::from_rust_map(l.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn annotations(&self) -> (annotations: Option<StringMap>)
        ensures
            self@.annotations.is_Some() == annotations.is_Some(),
            annotations.is_Some() ==> annotations.get_Some_0()@ == self@.annotations.get_Some_0(),
    {
        match &self.inner.annotations {
            Some(a) => Some(StringMap::from_rust_map(a.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn owner_references_only_contains(&self, owner_ref: OwnerReference) -> (res: bool)
        ensures
            res == self@.owner_references_only_contains(owner_ref@),
    {
        match &self.inner.owner_references {
            Some(owner_refs) => owner_refs.len() == 1 && owner_refs.contains(&owner_ref.into_kube()),
            None => false,
        }
    }

    #[verifier(external_body)]
    pub fn resource_version(&self) -> (version: Option<String>)
        ensures
            self@.resource_version.is_Some() == version.is_Some(),
            version.is_Some() ==> version.get_Some_0()@ == int_to_string_view(self@.resource_version.get_Some_0()),
    {
        match &self.inner.resource_version {
            Some(rv) => Some(String::from_rust_string(rv.to_string())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn has_deletion_timestamp(&self) -> (b: bool)
        ensures
            b == self@.deletion_timestamp.is_Some(),
    {
        self.inner.deletion_timestamp.is_some()
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
    pub fn add_annotation(&mut self, key: String, value: String)
        ensures
            self@ == old(self)@.add_annotation(key@, value@),
    {
        if self.inner.annotations.is_none() {
            let mut annotations = std::collections::BTreeMap::new();
            annotations.insert(key.into_rust_string(), value.into_rust_string());
            self.inner.annotations = Some(annotations);
        } else {
            self.inner.annotations.as_mut().unwrap().insert(key.into_rust_string(), value.into_rust_string());
        };
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

    #[verifier(external_body)]
    pub fn set_finalizers(&mut self, finalizers: Vec<String>)
        ensures
            self@ == old(self)@.set_finalizers(finalizers@.map_values(|s: String| s@)),
    {
        self.inner.finalizers = Some(
            finalizers.into_iter().map(|s: String| s.into_rust_string()).collect(),
        );
    }

    #[verifier(external_body)]
    pub fn unset_finalizers(&mut self)
        ensures
            self@ == old(self)@.unset_finalizers(),
    {
        self.inner.finalizers = None;
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
    pub resource_version: Option<ResourceVersion>, // make rv a nat so that it is easy to compare in spec/proof
    pub uid: Option<Uid>,
    pub labels: Option<Map<StringView, StringView>>,
    pub annotations: Option<Map<StringView, StringView>>,
    pub owner_references: Option<Seq<OwnerReferenceView>>,
    pub finalizers: Option<Seq<StringView>>,
    pub deletion_timestamp: Option<StringView>,
}

impl ObjectMetaView {
    pub open spec fn default() -> ObjectMetaView {
        ObjectMetaView {
            name: None,
            namespace: None,
            resource_version: None,
            uid: None,
            labels: None,
            annotations: None,
            owner_references: None,
            finalizers: None,
            deletion_timestamp: None,
        }
    }

    pub open spec fn owner_references_only_contains(self, owner_ref: OwnerReferenceView) -> bool {
        match self.owner_references {
            Some(owner_refs) => owner_refs == seq![owner_ref],
            None => false,
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

    pub open spec fn add_annotation(self, key: StringView, value: StringView) -> ObjectMetaView {
        let old_map = if self.annotations.is_None() {
            Map::empty()
        } else {
            self.annotations.get_Some_0()
        };
        ObjectMetaView {
            annotations: Some(old_map.insert(key, value)),
            ..self
        }
    }

    pub open spec fn set_resource_version(self, resource_version: ResourceVersion) -> ObjectMetaView {
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

    pub open spec fn set_finalizers(self, finalizers: Seq<StringView>) -> ObjectMetaView {
        ObjectMetaView {
            finalizers: Some(finalizers),
            ..self
        }
    }

    pub open spec fn unset_finalizers(self) -> ObjectMetaView {
        ObjectMetaView {
            finalizers: None,
            ..self
        }
    }

    pub open spec fn finalizers_as_set(self) -> Set<StringView> {
        if self.finalizers.is_None() {
            Set::empty()
        } else {
            self.finalizers.get_Some_0().to_set()
        }
    }

    pub open spec fn set_deletion_timestamp(self, deletion_timestamp: StringView) -> ObjectMetaView {
        ObjectMetaView {
            deletion_timestamp: Some(deletion_timestamp),
            ..self
        }
    }

    pub open spec fn well_formed(self) -> bool {
        &&& self.name.is_Some()
        &&& self.namespace.is_Some()
        &&& self.resource_version.is_Some()
        &&& self.uid.is_Some()
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
