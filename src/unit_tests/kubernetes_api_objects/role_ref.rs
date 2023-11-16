// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::role_binding::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for role ref
#[test]
#[verifier(external)]
pub fn test_default() {
    let role_ref = RoleRef::default();
    assert_eq!(role_ref.into_kube(), deps_hack::k8s_openapi::api::rbac::v1::RoleRef::default());
}

#[test]
#[verifier(external)]
pub fn test_set_api_group() {
    let mut role_ref = RoleRef::default();
    role_ref.set_api_group(new_strlit("api_group").to_string());
    assert_eq!("api_group".to_string(), role_ref.into_kube().api_group);
}

#[test]
#[verifier(external)]
pub fn test_set_kind() {
    let mut role_ref = RoleRef::default();
    role_ref.set_kind(new_strlit("kind").to_string());
    assert_eq!("kind".to_string(), role_ref.into_kube().kind);
}

#[test]
#[verifier(external)]
pub fn test_set_name() {
    let mut role_ref = RoleRef::default();
    role_ref.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), role_ref.into_kube().name);
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut role_ref = RoleRef::default();
    role_ref.set_api_group(new_strlit("api_group_2").to_string());
    role_ref.set_kind(new_strlit("kind_2").to_string());
    role_ref.set_name(new_strlit("name_2").to_string());
    let role_ref_clone = role_ref.clone();
    assert_eq!(role_ref.into_kube(), role_ref_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_role_ref = deps_hack::k8s_openapi::api::rbac::v1::RoleRef{
        api_group: "api_group".to_string(),
        kind: "kind".to_string(),
        name: "name".to_string(),
    };

    let role_ref = RoleRef::from_kube(kube_role_ref.clone());

    assert_eq!(role_ref.into_kube(),
                kube_role_ref);
}
}
