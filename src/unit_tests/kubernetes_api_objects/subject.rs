// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::role_binding::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for subject
#[test]
#[verifier(external)]
pub fn test_default() {
    let subject = Subject::default();
    assert_eq!(subject.into_kube(), deps_hack::k8s_openapi::api::rbac::v1::Subject::default());
}

#[test]
#[verifier(external)]
pub fn test_set_kind() {
    let mut subject = Subject::default();
    subject.set_kind(new_strlit("kind").to_string());
    assert_eq!("kind".to_string(), subject.into_kube().kind);
}

#[test]
#[verifier(external)]
pub fn test_set_name() {
    let mut subject = Subject::default();
    subject.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), subject.into_kube().name);
}

#[test]
#[verifier(external)]
pub fn test_set_namespace() {
    let mut subject = Subject::default();
    subject.set_namespace(new_strlit("namespace").to_string());
    assert_eq!("namespace".to_string(), subject.into_kube().namespace.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_subject = deps_hack::k8s_openapi::api::rbac::v1::Subject {
        kind: "kind".to_string(),
        name: "name".to_string(),
        namespace: Some("namespace".to_string()),
        ..Default::default()
    };

    let subject = Subject::from_kube(kube_subject.clone());

    assert_eq!(subject.into_kube(),
                deps_hack::k8s_openapi::api::rbac::v1::Subject {
                     kind: "kind".to_string(),
                     name: "name".to_string(),
                     namespace: Some("namespace".to_string()),
                     ..Default::default()
                });
}
}
