// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::service_account::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for service account
#[test]
#[verifier(external)]
pub fn test_default() {
    let service_account = ServiceAccount::default();
    assert_eq!(service_account.into_kube(), deps_hack::k8s_openapi::api::core::v1::ServiceAccount::default());
}

#[test]
#[verifier(external)]
pub fn test_set_metadata() {
    let mut service_account = ServiceAccount::default();
    let mut metadata = ObjectMeta::default();
    metadata.set_name(new_strlit("name").to_string());
    service_account.set_metadata(metadata.clone());
    assert_eq!(metadata.into_kube(), service_account.into_kube().metadata);
}

#[test]
#[verifier(external)]
pub fn test_metadata() {
    let mut service_account = ServiceAccount::default();
    let mut metadata = ObjectMeta::default();
    metadata.set_name(new_strlit("name").to_string());
    service_account.set_metadata(metadata.clone());
    assert_eq!(metadata.into_kube(), service_account.metadata().into_kube());
}

#[test]
#[verifier(external)]
pub fn test_api_resource() {
    let api_resource = ServiceAccount::api_resource();
    assert_eq!(api_resource.into_kube().kind, "ServiceAccount");
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut service_account = ServiceAccount::default();
    let mut metadata = ObjectMeta::default();
    metadata.set_name(new_strlit("name").to_string());
    service_account.set_metadata(metadata.clone());
    let service_account_clone = service_account.clone();
    assert_eq!(service_account.into_kube(), service_account_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_service_account = deps_hack::k8s_openapi::api::core::v1::ServiceAccount {
        metadata: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
            name: Some("name".to_string()),
            ..Default::default()
        },
        ..Default::default()
    };

    let service_account = ServiceAccount::from_kube(kube_service_account.clone());

    assert_eq!(
        service_account.into_kube(),
        kube_service_account
    );
}

#[test]
#[verifier(external)]
pub fn test_marshal() {
    let kube_service_account = deps_hack::k8s_openapi::api::core::v1::ServiceAccount {
        metadata: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
            name: Some("name".to_string()),
            ..Default::default()
        },
        ..Default::default()
    };

    let service_account = ServiceAccount::from_kube(kube_service_account.clone());

    assert_eq!(
        kube_service_account,
        ServiceAccount::unmarshal(service_account.marshal())
            .unwrap()
            .into_kube()
    );
}

}
