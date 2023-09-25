// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::owner_reference::*;
use crate::kubernetes_api_objects::resource::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

#[test]
#[verifier(external)]
pub fn test_set_name() {
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), object_meta.into_kube().name.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_namespace() {
    let mut object_meta = ObjectMeta::default();
    object_meta.set_namespace(new_strlit("namespace").to_string());
    assert_eq!("namespace".to_string(), object_meta.into_kube().namespace.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_labels() {
    let mut object_meta = ObjectMeta::default();
    let mut labels = StringMap::new();
    labels.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    object_meta.set_labels(labels.clone());
    assert_eq!(labels.into_rust_map(), object_meta.into_kube().labels.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_annotations() {
    let mut object_meta = ObjectMeta::default();
    let mut annotations = StringMap::new();
    annotations.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    object_meta.set_annotations(annotations.clone());
    assert_eq!(annotations.into_rust_map(), object_meta.into_kube().annotations.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_add_annotation() {
    let mut object_meta = ObjectMeta::default();
    let mut annotations = StringMap::new();
    annotations.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    let key = new_strlit("key").to_string();
    let value = new_strlit("value").to_string();
    object_meta.add_annotation(key, value);
    assert_eq!(annotations.into_rust_map(), object_meta.into_kube().annotations.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_finalizers() {
    let mut object_meta = ObjectMeta::default();
    // We use a closure to generate the Vec<vstd::string::String>
    // because we cannot use clone() of it.
    let finalizers_gen = || {
        let mut finalizers = Vec::new();
        finalizers.push(new_strlit("finalizer").to_string());
        finalizers
    };
    object_meta.set_finalizers(finalizers_gen());
    assert_eq!(finalizers_gen().into_iter().map(|s: String| s.into_rust_string()).collect::<Vec<_>>(), object_meta.into_kube().finalizers.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_unset_finalizers() {
    let mut object_meta = ObjectMeta::default();
    // We use a closure to generate the Vec<vstd::string::String>
    // because we cannot use clone() of it.
    let finalizers_gen = || {
        let mut finalizers = Vec::new();
        finalizers.push(new_strlit("finalizer").to_string());
        finalizers
    };
    object_meta.set_finalizers(finalizers_gen());
    object_meta.unset_finalizers();
    assert_eq!(None, object_meta.into_kube().finalizers);
}


#[test]
#[verifier(external)]
pub fn test_set_owner_references() {
    let mut object_meta = ObjectMeta::default();
    let own_refs_gen = || {
        let own_ref = deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference::default();
        let mut owner_references = Vec::new();
        owner_references.push(OwnerReference::from_kube(own_ref.clone()));
        owner_references
    };
    object_meta.set_owner_references(own_refs_gen());
    assert_eq!(own_refs_gen().into_iter().map(|s: OwnerReference| s.into_kube()).collect::<Vec<_>>(), object_meta.into_kube().owner_references.unwrap());
}

}
