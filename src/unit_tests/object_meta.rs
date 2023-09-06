// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

#[verifier(external)]
pub fn test() {
    println!("Running unit tests for kubernetes_api_objects::object_meta...");
    test_set_name();
    test_set_namespace();
}

#[verifier(external)]
pub fn test_set_name() {
    println!("Testing set_name()...");
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), object_meta.into_kube().name.unwrap());
}

#[verifier(external)]
pub fn test_set_namespace() {
    println!("Testing set_namespace()...");
    let mut object_meta = ObjectMeta::default();
    object_meta.set_namespace(new_strlit("namespace").to_string());
    assert_eq!("namespace".to_string(), object_meta.into_kube().namespace.unwrap());
}

}
