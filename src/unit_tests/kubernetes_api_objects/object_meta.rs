// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::owner_reference::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::vstd_ext::string_map::*;
use deps_hack::chrono::{DateTime, Utc};
use deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::Time;
use vstd::prelude::*;
use vstd::string::*;

verus! {
#[test]
#[verifier(external)]
pub fn test_default() {
    let object_meta = ObjectMeta::default();
    assert_eq!(
        object_meta.into_kube(),
        deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta::default()
    );
}

#[test]
#[verifier(external)]
pub fn test_set_name() {
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), object_meta.into_kube().name.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_name() {
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), object_meta.name().unwrap().into_rust_string());
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
pub fn test_namespace() {
    let mut object_meta = ObjectMeta::default();
    object_meta.set_namespace(new_strlit("namespace").to_string());
    assert_eq!("namespace".to_string(), object_meta.namespace().unwrap().into_rust_string());
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
pub fn test_labels() {
    let mut object_meta = ObjectMeta::default();
    let temp = object_meta.labels();
    if !temp.is_none() {
        panic!("Expected None")
    }
    let mut labels = StringMap::new();
    labels.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    object_meta.set_labels(labels.clone());
    assert_eq!(labels.into_rust_map(), object_meta.labels().unwrap().into_rust_map());
}

#[test]
#[verifier(external)]
pub fn test_owner_references_only_contains() {
    let mut object_meta = ObjectMeta::default();
    assert_eq!(false, object_meta.owner_references_only_contains(OwnerReference::from_kube(deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference::default())));
    let own_refs_gen = || {
        let own_ref = deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference::default();
        let mut owner_references = Vec::new();
        owner_references.push(OwnerReference::from_kube(own_ref.clone()));
        owner_references
    };
    object_meta.set_owner_references(own_refs_gen());
    assert_eq!(true, object_meta.owner_references_only_contains(OwnerReference::from_kube(deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference::default())));
}

#[test]
#[verifier(external)]
pub fn test_resource_version() {
    let object_meta = ObjectMeta::default();
    let temp = object_meta.resource_version();
    if !temp.is_none() {
        panic!("Expected None")
    }
    let object_meta = ObjectMeta::from_kube(deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
        resource_version: Some("resource_version".to_string()),
        ..Default::default()
    });
    assert_eq!("resource_version".to_string(), object_meta.resource_version().unwrap().into_rust_string());
}

#[test]
#[verifier(external)]
pub fn test_has_deletion_timestamp() {
    let object_meta = ObjectMeta::default();
    let time = Time(Utc::now());
    assert_eq!(false, object_meta.has_deletion_timestamp());
    let object_meta = ObjectMeta::from_kube(deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
        deletion_timestamp: Some(time),
        ..Default::default()
    });
    assert_eq!(true, object_meta.has_deletion_timestamp());
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
pub fn test_annotations() {
    let mut object_meta = ObjectMeta::default();
    let temp = object_meta.annotations();
    if !temp.is_none() {
        panic!("Expected None")
    }
    let mut annotations = StringMap::new();
    annotations.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    object_meta.set_annotations(annotations.clone());
    assert_eq!(annotations.into_rust_map(), object_meta.annotations().unwrap().into_rust_map());
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
pub fn test_clone(){
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    object_meta.set_namespace(new_strlit("namespace").to_string());
    object_meta.set_labels(StringMap::new());
    let object_meta_clone = object_meta.clone();
    assert_eq!(
        object_meta.into_kube(),
        object_meta_clone.into_kube()
    );
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

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_object_meta =
        deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
            name: Some("name".to_string()),
            namespace: Some("namespace".to_string()),
            labels: Some(
                vec![
                    (
                        "key".to_string(),
                        "value".to_string(),
                    ),
                ]
                .into_iter()
                .collect(),
            ),
            annotations: Some(
                vec![
                    (
                        "key".to_string(),
                        "value".to_string(),
                    ),
                ]
                .into_iter()
                .collect(),
            ),
            finalizers: Some(
                vec![
                    "finalizer".to_string(),
                ]
                .into_iter()
                .collect(),
            ),
            owner_references: Some(
                vec![
                    deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference::default(),
                ]
            ),
            ..Default::default()
        };

    let object_meta = ObjectMeta::from_kube(kube_object_meta.clone());
    assert_eq!(object_meta.into_kube(),
                kube_object_meta);
}
}
