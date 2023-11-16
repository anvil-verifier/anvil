// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::secret::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for secret
#[test]
#[verifier(external)]
pub fn test_default() {
    let secret = Secret::default();
    assert_eq!(secret.into_kube(), deps_hack::k8s_openapi::api::core::v1::Secret::default());
}

#[test]
#[verifier(external)]
pub fn test_set_metadata() {
    let mut secret = Secret::default();
    let mut metadata = ObjectMeta::default();
    metadata.set_name(new_strlit("name").to_string());
    metadata.set_namespace(new_strlit("namespace").to_string());
    secret.set_metadata(metadata.clone());
    assert_eq!(metadata.into_kube(), secret.into_kube().metadata);
}

#[test]
#[verifier(external)]
pub fn test_metadata() {
    let mut secret = Secret::default();
    let mut metadata = ObjectMeta::default();
    metadata.set_name(new_strlit("name").to_string());
    metadata.set_namespace(new_strlit("namespace").to_string());
    secret.set_metadata(metadata.clone());
    assert_eq!(metadata.into_kube(), secret.metadata().into_kube());
}

#[test]
#[verifier(external)]
pub fn test_set_data() {
    let mut secret = Secret::default();
    let mut data = StringMap::new();
    data.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    secret.set_data(data.clone());
    let mut binary_map = std::collections::BTreeMap::new();
    for (key, value) in data.into_rust_map() {
        binary_map.insert(key, deps_hack::k8s_openapi::ByteString(value.into_bytes()));
    }
    assert_eq!(binary_map, secret.into_kube().data.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_data() {
    let mut secret = Secret::default();
    let temp = secret.data();
    if !temp.is_none() {
        panic!("data should be None");
    }
    let mut data = StringMap::new();
    data.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    secret.set_data(data.clone());
    assert_eq!(data.into_rust_map(), secret.data().unwrap().into_rust_map());
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut secret = Secret::default();
    let mut metadata = ObjectMeta::default();
    metadata.set_name(new_strlit("name").to_string());
    metadata.set_namespace(new_strlit("namespace").to_string());
    secret.set_metadata(metadata.clone());
    let mut data = StringMap::new();
    data.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    secret.set_data(data.clone());
    let secret_clone = secret.clone();
    assert_eq!(secret.into_kube(), secret_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_api_resource() {
    let api_resource = Secret::api_resource();
    assert_eq!(api_resource.into_kube().kind, "Secret");
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_secret =
        deps_hack::k8s_openapi::api::core::v1::Secret {
            metadata: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                name: Some("name".to_string()),
                namespace: Some("namespace".to_string()),
                ..Default::default()
            },
            data: Some(
                std::collections::BTreeMap::from_iter(vec![(
                    "key".to_string(),
                    deps_hack::k8s_openapi::ByteString("value".to_string().into_bytes()),
                )]),
            ),
            ..Default::default()
        };

    let secret = Secret::from_kube(kube_secret.clone());

    assert_eq!(
        secret.into_kube(),
        kube_secret
    );
}

#[test]
#[verifier(external)]
pub fn test_marshal() {
    let kube_secret =
        deps_hack::k8s_openapi::api::core::v1::Secret {
            metadata: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                name: Some("name".to_string()),
                namespace: Some("namespace".to_string()),
                ..Default::default()
            },
            data: Some(
                std::collections::BTreeMap::from_iter(vec![(
                    "key".to_string(),
                    deps_hack::k8s_openapi::ByteString("value".to_string().into_bytes()),
                )]),
            ),
            ..Default::default()
        };

    let secret = Secret::from_kube(kube_secret.clone());

    assert_eq!(
        kube_secret,
        Secret::unmarshal(secret.marshal())
            .unwrap()
            .into_kube()
    );
}
}
