// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

#[test]
#[verifier(external)]
pub fn test_set_name() {
    println!("Testing set_name()...");
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
pub fn test_set_generate_name() {
    let mut object_meta = ObjectMeta::default();
    object_meta.set_generate_name(new_strlit("generate_name").to_string());
    assert_eq!("generate_name".to_string(), object_meta.into_kube().generate_name.unwrap());
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


}
