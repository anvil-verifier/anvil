// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::cluster_role_binding::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::kubernetes_api_objects::role_binding::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for cluster role binding
#[test]
#[verifier(external)]
pub fn test_default() {
    let cluster_role_binding = ClusterRoleBinding::default();
    assert_eq!(cluster_role_binding.into_kube(), deps_hack::k8s_openapi::api::rbac::v1::ClusterRoleBinding::default());
}

#[test]
#[verifier(external)]
pub fn test_set_metadata() {
    let mut cluster_role_binding = ClusterRoleBinding::default();
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    cluster_role_binding.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), cluster_role_binding.into_kube().metadata);
}

#[test]
#[verifier(external)]
pub fn test_metadata() {
    let mut cluster_role_binding = ClusterRoleBinding::default();
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    cluster_role_binding.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), cluster_role_binding.metadata().into_kube());
}

#[test]
#[verifier(external)]
pub fn test_set_role_ref() {
    let mut cluster_role_binding = ClusterRoleBinding::default();
    let mut role_ref = RoleRef::default();
    role_ref.set_api_group(new_strlit("api_group").to_string());
    role_ref.set_kind(new_strlit("kind").to_string());
    role_ref.set_name(new_strlit("name").to_string());
    cluster_role_binding.set_role_ref(role_ref.clone());
    assert_eq!(role_ref.into_kube(), cluster_role_binding.into_kube().role_ref);
}

#[test]
#[verifier(external)]
pub fn test_set_subjects() {
    let mut cluster_role_binding = ClusterRoleBinding::default();
    let subjects_gen = || {
        let mut subjects = Vec::new();
        let mut subject = Subject::default();
        subject.set_kind(new_strlit("kind").to_string());
        subject.set_name(new_strlit("name").to_string());
        subject.set_namespace(new_strlit("namespace").to_string());
        subjects.push(subject);
        subjects
    };

    cluster_role_binding.set_subjects(subjects_gen());
    assert_eq!(
        subjects_gen()
            .into_iter()
            .map(|s: Subject| s.into_kube())
            .collect::<Vec<_>>(),
        cluster_role_binding.into_kube().subjects.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_api_resource(){
    let api_resource = ClusterRoleBinding::api_resource();
    assert_eq!(api_resource.into_kube().kind, "ClusterRoleBinding");
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_cluster_role_binding = deps_hack::k8s_openapi::api::rbac::v1::ClusterRoleBinding {
        metadata: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
            name: Some("name".to_string()),
            ..Default::default()
        },
        role_ref: deps_hack::k8s_openapi::api::rbac::v1::RoleRef {
            api_group: "api_group".to_string(),
            kind: "kind".to_string(),
            name: "name".to_string(),
        },
        subjects: Some(vec![deps_hack::k8s_openapi::api::rbac::v1::Subject {
            kind: "kind".to_string(),
            name: "name".to_string(),
            namespace: Some("namespace".to_string()),
            ..Default::default()
        }]),
        ..Default::default()
    };

    let cluster_role_binding = ClusterRoleBinding::from_kube(
        kube_cluster_role_binding.clone(),
    );

    assert_eq!(cluster_role_binding.into_kube(),
                kube_cluster_role_binding);
}
}
