// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{owner_reference::*, resource::*};
use crate::kubernetes_api_objects::spec::object_meta::*;
use crate::vstd_ext::{string_map::*, string_view::*};
use vstd::{prelude::*, string::*};

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
        ensures object_meta@ == ObjectMetaView::default(),
    {
        ObjectMeta {
            inner: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures s@ == self@,
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
    pub fn finalizers(&self) -> (finalizers: Option<Vec<String>>)
        ensures
            self@.finalizers.is_Some() == finalizers.is_Some(),
            finalizers.is_Some() ==> finalizers.get_Some_0()@.map_values(|s: String| s@) == self@.finalizers.get_Some_0(),
    {
        match &self.inner.finalizers {
            Some(o) => Some(o.into_iter().map(|item| String::from_rust_string(item.clone())).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn owner_references(&self) -> (owner_references: Option<Vec<OwnerReference>>)
        ensures
            self@.owner_references.is_Some() == owner_references.is_Some(),
            owner_references.is_Some() ==> owner_references.get_Some_0()@.map_values(|o: OwnerReference| o@) == self@.owner_references.get_Some_0(),
    {
        match &self.inner.owner_references {
            Some(o) => Some(o.into_iter().map(|item| OwnerReference::from_kube(item.clone())).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn owner_references_only_contains(&self, owner_ref: OwnerReference) -> (res: bool)
        ensures res == self@.owner_references_only_contains(owner_ref@),
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
    pub fn has_some_resource_version(&self) -> (b: bool)
        ensures
            self@.resource_version.is_Some() == b,
    {
        self.inner.resource_version.is_some()
    }

    // We need this seemingly redundant function because of the inconsistency
    // between the actual resource version and its spec-level encoding:
    // one is String while the other is an int.
    // If we want to reason about the exec code that compares two ObjectMeta's rv,
    // we need to call this function to prove the result of the comparison is the
    // same as comparing the two spec-level rv (two ints).
    #[verifier(external_body)]
    pub fn resource_version_eq(&self, other: &ObjectMeta) -> (b: bool)
        ensures b == (self@.resource_version == other@.resource_version)
    {
        self.inner.resource_version == other.inner.resource_version
    }

    #[verifier(external_body)]
    pub fn has_some_uid(&self) -> (b: bool)
        ensures
            self@.uid.is_Some() == b,
    {
        self.inner.uid.is_some()
    }

    // We need this seemingly redundant function for the same
    // reason of resource_version_eq.
    #[verifier(external_body)]
    pub fn uid_eq(&self, other: &ObjectMeta) -> (b: bool)
        ensures b == (self@.uid == other@.uid)
    {
        self.inner.uid == other.inner.uid
    }

    #[verifier(external_body)]
    pub fn has_deletion_timestamp(&self) -> (b: bool)
        ensures b == self@.deletion_timestamp.is_Some(),
    {
        self.inner.deletion_timestamp.is_some()
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.set_name(name@),
    {
        self.inner.name = Some(name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_namespace(&mut self, namespace: String)
        ensures self@ == old(self)@.set_namespace(namespace@),
    {
        self.inner.namespace = Some(namespace.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_labels(&mut self, labels: StringMap)
        ensures self@ == old(self)@.set_labels(labels@),
    {
        self.inner.labels = Some(labels.into_rust_map());
    }

    #[verifier(external_body)]
    pub fn set_annotations(&mut self, annotations: StringMap)
        ensures self@ == old(self)@.set_annotations(annotations@),
    {
        self.inner.annotations = Some(annotations.into_rust_map());
    }

    #[verifier(external_body)]
    pub fn add_annotation(&mut self, key: String, value: String)
        ensures self@ == old(self)@.add_annotation(key@, value@),
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
        ensures self@ == old(self)@.set_owner_references(owner_references@.map_values(|o: OwnerReference| o@)),
    {
        self.inner.owner_references = Some(owner_references.into_iter().map(|o: OwnerReference| o.into_kube()).collect());
    }

    #[verifier(external_body)]
    pub fn set_finalizers(&mut self, finalizers: Vec<String>)
        ensures self@ == old(self)@.set_finalizers(finalizers@.map_values(|s: String| s@)),
    {
        self.inner.finalizers = Some(finalizers.into_iter().map(|s: String| s.into_rust_string()).collect());
    }

    #[verifier(external_body)]
    pub fn unset_finalizers(&mut self)
        ensures self@ == old(self)@.unset_finalizers(),
    {
        self.inner.finalizers = None;
    }
}

#[verifier(external)]
impl ResourceWrapper<deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta> for ObjectMeta {
    fn from_kube(inner: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta) -> ObjectMeta { ObjectMeta { inner: inner } }

    fn into_kube(self) -> deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta { self.inner }
}

}
