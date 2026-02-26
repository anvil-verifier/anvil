// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::{owner_reference::*, resource::*};
use crate::kubernetes_api_objects::spec::object_meta::*;
use crate::vstd_ext::{string_map::*, string_view::*};
use vstd::prelude::*;

verus! {

// ObjectMeta contains the metadata that all Kubernetes resource objects must have,
// including name, namespace, uid, and so on.
//
// This definition is a wrapper of ObjectMeta defined at
// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/apimachinery/pkg/apis/meta/v1/object_meta.rs.
// It is supposed to be used in exec controller code.
//
// More detailed information: https://kubernetes.io/docs/reference/kubernetes-api/common-definitions/object-meta/.

implement_field_wrapper_type!(
    ObjectMeta,
    deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta,
    ObjectMetaView
);

impl ObjectMeta {
    #[verifier(external_body)]
    pub fn name(&self) -> (name: Option<String>)
        ensures self@.name == name.deep_view()
    {
        self.inner.name.clone()
    }

    #[verifier(external_body)]
    pub fn namespace(&self) -> (namespace: Option<String>)
        ensures self@.namespace == namespace.deep_view()
    {
        self.inner.namespace.clone()
    }

    #[verifier(external_body)]
    pub fn namespace_eq(&self, other: &ObjectMeta) -> (b: bool)
        ensures b == (self@.namespace == other@.namespace)
    {
        self.inner.namespace == other.inner.namespace
    }

    #[verifier(external_body)]
    pub fn generated_name(&self) -> (generate_name: Option<String>)
        ensures self@.generate_name == generate_name.deep_view()
    {
        self.inner.generate_name.clone()
    }

    #[verifier(external_body)]
    pub fn labels(&self) -> (labels: Option<StringMap>)
        ensures
            self@.labels == labels.deep_view(),
            labels is Some ==> labels->0@.dom().finite(),
    {
        match &self.inner.labels {
            Some(l) => Some(StringMap::from_rust_map(l.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn annotations(&self) -> (annotations: Option<StringMap>)
        ensures
            self@.annotations == annotations.deep_view(),
            annotations is Some ==> annotations->0@.dom().finite(),
    {
        match &self.inner.annotations {
            Some(a) => Some(StringMap::from_rust_map(a.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn finalizers(&self) -> (finalizers: Option<Vec<String>>)
        ensures self@.finalizers == finalizers.deep_view()
    {
        self.inner.finalizers.clone()
    }

    #[verifier(external_body)]
    pub fn owner_references(&self) -> (owner_references: Option<Vec<OwnerReference>>)
        ensures self@.owner_references == owner_references.deep_view()
    {
        match &self.inner.owner_references {
            Some(o) => Some(o.into_iter().map(|item| OwnerReference::from_kube(item.clone())).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn owner_references_contains(&self, owner_ref: &OwnerReference) -> (res: bool)
        ensures res == self@.owner_references_contains(owner_ref@),
    {
        match &self.inner.owner_references {
            Some(owner_refs) => owner_refs.contains(owner_ref.as_kube_ref()),
            None => false,
        }
    }

    #[verifier(external_body)]
    pub fn owner_references_only_contains(&self, owner_ref: &OwnerReference) -> (res: bool)
        ensures res == self@.owner_references_only_contains(owner_ref@),
    {
        match &self.inner.owner_references {
            Some(owner_refs) => owner_refs.len() == 1 && owner_refs.contains(owner_ref.as_kube_ref()),
            None => false,
        }
    }

    #[verifier(external_body)]
    pub fn resource_version(&self) -> (resource_version: Option<String>)
        ensures
            self@.resource_version is Some == resource_version is Some,
            resource_version is Some ==> resource_version->0@ == int_to_string_view(self@.resource_version->0),
    {
        self.inner.resource_version.clone()
    }

    #[verifier(external_body)]
    pub fn has_some_resource_version(&self) -> (b: bool)
        ensures self@.resource_version is Some == b
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
        ensures self@.uid is Some == b,
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
        ensures b == self@.deletion_timestamp is Some,
    {
        self.inner.deletion_timestamp.is_some()
    }

    pub fn well_formed_for_namespaced(&self) -> (b: bool)
        ensures b == self@.well_formed_for_namespaced(),
    {
        self.name().is_some()
        && self.namespace().is_some()
        && self.resource_version().is_some()
        && self.has_some_uid()
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.with_name(name@),
    {
        self.inner.name = Some(name);
    }

    #[verifier(external_body)]
    pub fn set_generate_name(&mut self, generate_name: String)
        ensures self@ == old(self)@.with_generate_name(generate_name@),
    {
        self.inner.generate_name = Some(generate_name);
    }

    #[verifier(external_body)]
    pub fn set_namespace(&mut self, namespace: String)
        ensures self@ == old(self)@.with_namespace(namespace@),
    {
        self.inner.namespace = Some(namespace);
    }

    #[verifier(external_body)]
    pub fn set_labels(&mut self, labels: StringMap)
        ensures self@ == old(self)@.with_labels(labels@),
    {
        self.inner.labels = Some(labels.into_rust_map());
    }

    #[verifier(external_body)]
    pub fn add_label(&mut self, key: String, value: String)
        ensures self@ == old(self)@.add_label(key@, value@),
    {
        if self.inner.labels.is_none() {
            let mut labels = std::collections::BTreeMap::new();
            labels.insert(key, value);
            self.inner.labels = Some(labels);
        } else {
            self.inner.labels.as_mut().unwrap().insert(key, value);
        };
    }

    #[verifier(external_body)]
    pub fn remove_label(&mut self, key: String)
        ensures self@ == old(self)@.without_label(key@),
    {
        if self.inner.labels.is_some() {
            self.inner.labels.as_mut().unwrap().remove(&key);
        }
    }

    #[verifier(external_body)]
    pub fn set_annotations(&mut self, annotations: StringMap)
        ensures self@ == old(self)@.with_annotations(annotations@),
    {
        self.inner.annotations = Some(annotations.into_rust_map());
    }

    #[verifier(external_body)]
    pub fn add_annotation(&mut self, key: String, value: String)
        ensures self@ == old(self)@.add_annotation(key@, value@),
    {
        if self.inner.annotations.is_none() {
            let mut annotations = std::collections::BTreeMap::new();
            annotations.insert(key, value);
            self.inner.annotations = Some(annotations);
        } else {
            self.inner.annotations.as_mut().unwrap().insert(key, value);
        };
    }

    #[verifier(external_body)]
    pub fn set_owner_references(&mut self, owner_references: Vec<OwnerReference>)
        ensures self@ == old(self)@.with_owner_references(owner_references.deep_view()),
    {
        self.inner.owner_references = Some(owner_references.into_iter().map(|o: OwnerReference| o.into_kube()).collect());
    }

    #[verifier(external_body)]
    pub fn set_finalizers(&mut self, finalizers: Vec<String>)
        ensures self@ == old(self)@.with_finalizers(finalizers.deep_view()),
    {
        self.inner.finalizers = Some(finalizers);
    }

    #[verifier(external_body)]
    pub fn unset_finalizers(&mut self)
        ensures self@ == old(self)@.without_finalizers(),
    {
        self.inner.finalizers = None;
    }

    #[verifier(external_body)]
    pub fn unset_deletion_timestamp(&mut self)
        ensures self@ == old(self)@.without_deletion_timestamp(),
    {
        self.inner.deletion_timestamp = None;
    }
}

}
