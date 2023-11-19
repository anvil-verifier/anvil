// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::volume::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for ObjectFieldSelector
#[test]
#[verifier(external)]
pub fn test_set_field_path() {
    let mut object_field_selector = ObjectFieldSelector::default();
    object_field_selector.set_field_path(new_strlit("field_path").to_string());
    assert_eq!("field_path".to_string(), object_field_selector.into_kube().field_path);
}

#[test]
#[verifier(external)]
pub fn test_set_api_version() {
    let mut object_field_selector = ObjectFieldSelector::default();
    object_field_selector.set_api_version(new_strlit("api_version").to_string());
    assert_eq!("api_version".to_string(), object_field_selector.into_kube().api_version.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_default() {
    let object_field_selector = ObjectFieldSelector::default();
    assert_eq!(object_field_selector.into_kube(), deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector::default());
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut object_field_selector = ObjectFieldSelector::default();
    object_field_selector.set_field_path(new_strlit("field_path").to_string());
    object_field_selector.set_api_version(new_strlit("api_version").to_string());
    let object_field_selector_clone = object_field_selector.clone();
    assert_eq!(object_field_selector.into_kube(), object_field_selector_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_object_field_selector = deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector{
        api_version: Some("api_version".to_string()),
        field_path: "field_path".to_string(),
    };

    let object_field_selector = ObjectFieldSelector::from_kube(kube_object_field_selector.clone());

    assert_eq!(object_field_selector.into_kube(),
                kube_object_field_selector);
}

}
