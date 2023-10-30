// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::container::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::pod::*;
use crate::kubernetes_api_objects::resource::*;
use crate::kubernetes_api_objects::volume::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for scret projection
#[test]
#[verifier(external)]
pub fn test_default() {
    let secret_projection = SecretProjection::default();
    assert_eq!(secret_projection.into_kube(), deps_hack::k8s_openapi::api::core::v1::SecretProjection::default());
}

#[test]
#[verifier(external)]
pub fn test_set_name() {
    let mut secret_projection = SecretProjection::default();
    secret_projection.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), secret_projection.into_kube().name.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_items() {
    let mut secret_projection = SecretProjection::default();
    let key_to_paths_gen = || {
        let mut key_to_path_1 = KeyToPath::default();
        let mut key_to_path_2 = KeyToPath::default();
        let mut key_to_paths = Vec::new();
        key_to_path_1.set_key(new_strlit("key1").to_string());
        key_to_path_1.set_path(new_strlit("path1").to_string());
        key_to_path_2.set_key(new_strlit("key2").to_string());
        key_to_path_2.set_path(new_strlit("path2").to_string());
        key_to_paths.push(key_to_path_1);
        key_to_paths.push(key_to_path_2);
        key_to_paths
    };
    secret_projection.set_items(key_to_paths_gen());
    assert_eq!(
        key_to_paths_gen()
            .into_iter()
            .map(|s: KeyToPath| s.into_kube())
            .collect::<Vec<_>>(),
        secret_projection.into_kube().items.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let secret_projection = SecretProjection::from_kube(deps_hack::k8s_openapi::api::core::v1::SecretProjection{
        name: Some("name".to_string()),
        items: Some(vec![
            deps_hack::k8s_openapi::api::core::v1::KeyToPath{
                key: "key1".to_string(),
                path: "path1".to_string(),
                ..Default::default()
            },
            deps_hack::k8s_openapi::api::core::v1::KeyToPath{
                key: "key2".to_string(),
                path: "path2".to_string(),
                ..Default::default()
            }
        ]),
        ..Default::default()
    });

    assert_eq!(
        secret_projection.into_kube(),
        deps_hack::k8s_openapi::api::core::v1::SecretProjection{
            name: Some("name".to_string()),
            items: Some(vec![
                deps_hack::k8s_openapi::api::core::v1::KeyToPath{
                    key: "key1".to_string(),
                    path: "path1".to_string(),
                    ..Default::default()
                },
                deps_hack::k8s_openapi::api::core::v1::KeyToPath{
                    key: "key2".to_string(),
                    path: "path2".to_string(),
                    ..Default::default()
                }
            ]),
            ..Default::default()
        }
    );
}
}
