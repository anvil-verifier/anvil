// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::kubernetes_api_objects::volume::*;
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

}
