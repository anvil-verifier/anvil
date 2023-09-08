// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

// #[verifier(external)]
// pub fn test() {
//     println!("Running unit tests for kubernetes_api_objects::object_meta...");
//     test_set_name();
//     test_set_namespace();
// }

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
    println!("Testing set_namespace()...");
    let mut object_meta = ObjectMeta::default();
    object_meta.set_namespace(new_strlit("namespace").to_string());
    assert_eq!("namespace".to_string(), object_meta.into_kube().namespace.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_generate_name() {
    println!("Testing set_generate_name()...");
    let mut object_meta = ObjectMeta::default();
    object_meta.set_generate_name(new_strlit("generate_name").to_string());
    assert_eq!("generate_name".to_string(), object_meta.into_kube().generate_name.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_labels() {
    println!("Testing set_labels()...");
    let mut object_meta = ObjectMeta::default();
    let mut labels = StringMap::new();
    labels.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    object_meta.set_labels(labels);
    assert_eq!(1, object_meta.into_kube().labels.unwrap().len());
    // assert_eq!("value".to_string(), object_meta.into_kube().labels.unwrap().get("key").unwrap().to_string());
}

#[test]
#[verifier(external)]
pub fn test_set_add_annotations() {
    println!("Testing set_annotations()...");
    let mut object_meta = ObjectMeta::default();
    let mut annotations = StringMap::new();
    annotations.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    object_meta.set_annotations(annotations);
    assert_eq!(1, object_meta.into_kube().annotations.unwrap().len());
    // assert_eq!("value".to_string(), object_meta.into_kube().annotations.unwrap().get("key").unwrap().to_string());
    // println!("Testing add_annotations()...");
    // object_meta.add_annotation(new_strlit("key2").to_string(), new_strlit("value2").to_string());
    // assert_eq!(2, object_meta.into_kube().annotations.unwrap().len());
    // assert_eq!("value2".to_string(), object_meta.into_kube().annotations.unwrap().get("key2").unwrap().to_string());
}

#[test]
#[verifier(external)]
pub fn test_set_owner_references() {
  //@TODO  Need some discussion about this because we do not have set functions to ownerreference
}

#[test]
#[verifier(external)]
pub fn test_set_finalizers() {
    println!("Testing set_finalizers()...");
    let mut object_meta = ObjectMeta::default();
    let mut finalizers = Vec::new();
    finalizers.push(new_strlit("finalizer").to_string());
    object_meta.set_finalizers(finalizers);
    assert_eq!(1, object_meta.into_kube().finalizers.unwrap().len());
    // assert_eq!("finalizer".to_string(), object_meta.into_kube().finalizers.unwrap().get(0).unwrap().to_string());
    // println!("Testing unset_finalizers()...");
    // object_meta.unset_finalizers();
    // assert_eq!( None, object_meta.into_kube().finalizers);

}


}
