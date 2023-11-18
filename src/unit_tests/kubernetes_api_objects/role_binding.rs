// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::role_binding::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for role binding
#[test]
#[verifier(external)]
pub fn test_default() {
    let role_binding = RoleBinding::default();
    assert_eq!(role_binding.into_kube(), deps_hack::k8s_openapi::api::rbac::v1::RoleBinding::default());
}

#[test]
#[verifier(external)]
pub fn test_set_metadata() {
    let mut role_binding = RoleBinding::default();
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    object_meta.set_namespace(new_strlit("namespace").to_string());
    role_binding.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), role_binding.into_kube().metadata);
}

#[test]
#[verifier(external)]
pub fn test_metadata() {
    let mut role_binding = RoleBinding::default();
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    object_meta.set_namespace(new_strlit("namespace").to_string());
    role_binding.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), role_binding.metadata().into_kube());
}

#[test]
#[verifier(external)]
pub fn test_set_role_ref() {
    let mut role_binding = RoleBinding::default();
    let mut role_ref = RoleRef::default();
    role_ref.set_api_group(new_strlit("api_group").to_string());
    role_ref.set_kind(new_strlit("kind").to_string());
    role_ref.set_name(new_strlit("name").to_string());
    role_binding.set_role_ref(role_ref.clone());
    assert_eq!(role_ref.into_kube(), role_binding.into_kube().role_ref);
}

#[test]
#[verifier(external)]
pub fn test_set_subjects() {
    let mut role_binding = RoleBinding::default();
    let subject_gen = || {
        let mut subject_1 = Subject::default();
        let mut subject_2 = Subject::default();
        let mut subjects = Vec::new();
        subject_1.set_kind(new_strlit("kind1").to_string());
        subject_1.set_name(new_strlit("name1").to_string());
        subject_1.set_namespace(new_strlit("namespace1").to_string());
        subject_2.set_kind(new_strlit("kind2").to_string());
        subject_2.set_name(new_strlit("name2").to_string());
        subject_2.set_namespace(new_strlit("namespace2").to_string());
        subjects.push(subject_1);
        subjects.push(subject_2);
        subjects
    };
    role_binding.set_subjects(subject_gen());
    assert_eq!(
        subject_gen()
            .into_iter()
            .map(|s: Subject| s.into_kube())
            .collect::<Vec<_>>(),
        role_binding.into_kube().subjects.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut role_binding = RoleBinding::default();
    let mut object_meta = ObjectMeta::default();
    let mut role_ref = RoleRef::default();
    let subject_gen = || {
        let mut subject_1 = Subject::default();
        let mut subject_2 = Subject::default();
        let mut subjects = Vec::new();
        subject_1.set_kind(new_strlit("kind1").to_string());
        subject_1.set_name(new_strlit("name1").to_string());
        subject_1.set_namespace(new_strlit("namespace1").to_string());
        subject_2.set_kind(new_strlit("kind2").to_string());
        subject_2.set_name(new_strlit("name2").to_string());
        subject_2.set_namespace(new_strlit("namespace2").to_string());
        subjects.push(subject_1);
        subjects.push(subject_2);
        subjects
    };
    object_meta.set_name(new_strlit("name").to_string());
    object_meta.set_namespace(new_strlit("namespace").to_string());
    role_ref.set_api_group(new_strlit("api_group").to_string());
    role_ref.set_kind(new_strlit("kind").to_string());
    role_ref.set_name(new_strlit("name").to_string());
    role_binding.set_metadata(object_meta.clone());
    role_binding.set_role_ref(role_ref.clone());
    role_binding.set_subjects(subject_gen());
    let role_binding_clone = role_binding.clone();
    assert_eq!(role_binding.into_kube(), role_binding_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_api_resource(){
    let api_resource = RoleBinding::api_resource();
    assert_eq!(api_resource.into_kube().kind, "RoleBinding");
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_role_binding =
        deps_hack::k8s_openapi::api::rbac::v1::RoleBinding {
            metadata:
                deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                    name: Some("name".to_string()),
                    namespace: Some("namespace".to_string()),
                    ..Default::default()
                },
            role_ref:
                deps_hack::k8s_openapi::api::rbac::v1::RoleRef {
                    api_group: "api_group".to_string(),
                    kind: "kind".to_string(),
                    name: "name".to_string(),
                    ..Default::default()
                },
            subjects: Some(vec![
                deps_hack::k8s_openapi::api::rbac::v1::Subject {
                    kind: "kind1".to_string(),
                    name: "name1".to_string(),
                    namespace: Some("namespace1".to_string()),
                    ..Default::default()
                },
                deps_hack::k8s_openapi::api::rbac::v1::Subject {
                    kind: "kind2".to_string(),
                    name: "name2".to_string(),
                    namespace: Some("namespace2".to_string()),
                    ..Default::default()
                },
            ]),
            ..Default::default()
        };

    let role_binding = RoleBinding::from_kube(kube_role_binding.clone());

    assert_eq!(
        role_binding.into_kube(),
        kube_role_binding
    );
}

#[test]
#[verifier(external)]
pub fn test_marshal() {
    let kube_role_binding =
        deps_hack::k8s_openapi::api::rbac::v1::RoleBinding {
            metadata:
                deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                    name: Some("name".to_string()),
                    namespace: Some("namespace".to_string()),
                    ..Default::default()
                },
            role_ref:
                deps_hack::k8s_openapi::api::rbac::v1::RoleRef {
                    api_group: "api_group".to_string(),
                    kind: "kind".to_string(),
                    name: "name".to_string(),
                    ..Default::default()
                },
            subjects: Some(vec![
                deps_hack::k8s_openapi::api::rbac::v1::Subject {
                    kind: "kind1".to_string(),
                    name: "name1".to_string(),
                    namespace: Some("namespace1".to_string()),
                    ..Default::default()
                },
                deps_hack::k8s_openapi::api::rbac::v1::Subject {
                    kind: "kind2".to_string(),
                    name: "name2".to_string(),
                    namespace: Some("namespace2".to_string()),
                    ..Default::default()
                },
            ]),
            ..Default::default()
        };

    let role_binding = RoleBinding::from_kube(kube_role_binding.clone());

    assert_eq!(
        kube_role_binding,
        RoleBinding::unmarshal(role_binding.marshal()).unwrap().into_kube()
    );
}
}
