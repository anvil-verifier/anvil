// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, label_selector::*, object_meta::*, persistent_volume_claim::*,
    resource::*,
};
use crate::vstd_ext::string_map::*;
use std::collections::BTreeMap;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for persistent volume claim
#[test]
#[verifier(external)]
pub fn test_default() {
    let persistent_volume_claim = PersistentVolumeClaim::default();
    assert_eq!(
        persistent_volume_claim.into_kube(),
        deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim::default()
    );
}

#[test]
#[verifier(external)]
pub fn test_set_metadata() {
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    object_meta.set_namespace(new_strlit("namespace").to_string());
    let mut persistent_volume_claim = PersistentVolumeClaim::default();
    persistent_volume_claim.set_metadata(object_meta.clone());
    assert_eq!(
        object_meta.into_kube(),
        persistent_volume_claim.into_kube().metadata
    );
}

#[test]
#[verifier(external)]
pub fn test_metadata() {
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    object_meta.set_namespace(new_strlit("namespace").to_string());
    let mut persistent_volume_claim = PersistentVolumeClaim::default();
    persistent_volume_claim.set_metadata(object_meta.clone());
    assert_eq!(
        object_meta.into_kube(),
        persistent_volume_claim.metadata().into_kube()
    );
}

#[test]
#[verifier(external)]
pub fn test_set_spec() {
    let mut persistent_volume_claim_spec = PersistentVolumeClaimSpec::default();
    persistent_volume_claim_spec.set_access_modes(vec![new_strlit("ReadWriteOnce").to_string()]);

    let mut persistent_volume_claim = PersistentVolumeClaim::default();
    persistent_volume_claim.set_spec(persistent_volume_claim_spec.clone());
    assert_eq!(
        persistent_volume_claim_spec.into_kube(),
        persistent_volume_claim.into_kube().spec.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_spec() {
    let mut persistent_volume_claim_spec = PersistentVolumeClaimSpec::default();
    persistent_volume_claim_spec.set_access_modes(vec![new_strlit("ReadWriteOnce").to_string()]);
    let mut persistent_volume_claim = PersistentVolumeClaim::default();
    let temp = persistent_volume_claim.spec();
    if !temp.is_none() {
        panic!("Expected None")
    }
    persistent_volume_claim.set_spec(persistent_volume_claim_spec.clone());
    assert_eq!(
        persistent_volume_claim_spec.into_kube(),
        persistent_volume_claim.spec().unwrap().into_kube()
    );
}

#[test]
#[verifier(external)]
pub fn test_api_resource(){
    let api_resource = PersistentVolumeClaim::api_resource();
    assert_eq!(api_resource.into_kube().kind, "PersistentVolumeClaim");
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_persistent_volume_claim =
        deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim {
            metadata:
                deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                    name: Some("name".to_string()),
                    namespace: Some("namespace".to_string()),
                    ..Default::default()
                },
            spec: Some(
                deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaimSpec {
                    access_modes: Some(
                        vec![
                            "ReadWriteOnce".to_string(),
                            "ReadOnlyMany".to_string(),
                        ]
                        .into_iter()
                        .collect(),
                    ),
                    resources: Some(
                        deps_hack::k8s_openapi::api::core::v1::ResourceRequirements {
                            requests: Some(
                                BTreeMap::from([
                                    (
                                        "storage".to_string(), deps_hack::k8s_openapi::apimachinery::pkg::api::resource::Quantity("1Gi".to_string())
                                    ),
                                ])
                            ),
                            ..Default::default()
                        },
                    ),
                    storage_class_name: Some("storage_class_name".to_string()),
                    ..Default::default()
                },
            ),
            ..Default::default()
        };

    let persistent_volume_claim = PersistentVolumeClaim::from_kube(kube_persistent_volume_claim.clone());

    assert_eq!(
        persistent_volume_claim.into_kube(),
        kube_persistent_volume_claim
    );
}

#[test]
#[verifier(external)]
pub fn test_marshal() {
    let kube_persistent_volume_claim =
        deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim {
            metadata:
                deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                    name: Some("name".to_string()),
                    namespace: Some("namespace".to_string()),
                    ..Default::default()
                },
            spec: Some(
                deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaimSpec {
                    access_modes: Some(
                        vec![
                            "ReadWriteOnce".to_string(),
                            "ReadOnlyMany".to_string(),
                        ]
                        .into_iter()
                        .collect(),
                    ),
                    resources: Some(
                        deps_hack::k8s_openapi::api::core::v1::ResourceRequirements {
                            requests: Some(
                                BTreeMap::from([
                                    (
                                        "storage".to_string(), deps_hack::k8s_openapi::apimachinery::pkg::api::resource::Quantity("1Gi".to_string())
                                    ),
                                ])
                            ),
                            ..Default::default()
                        },
                    ),
                    storage_class_name: Some("storage_class_name".to_string()),
                    ..Default::default()
                },
            ),
            ..Default::default()
        };

    let persistent_volume_claim = PersistentVolumeClaim::from_kube(kube_persistent_volume_claim.clone());

    assert_eq!(
        kube_persistent_volume_claim,
        PersistentVolumeClaim::unmarshal(persistent_volume_claim.marshal()).unwrap().into_kube()
    );
}
}
