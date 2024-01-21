use std::collections::BTreeMap;

// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, label_selector::*, object_meta::*, persistent_volume_claim::*,
    resource::*, resource_requirements::*,
};
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for persistent volume claim spec
#[test]
#[verifier(external)]
pub fn test_default() {
    let persistent_volume_claim_spec = PersistentVolumeClaimSpec::default();
    assert_eq!(
        persistent_volume_claim_spec.into_kube(),
        deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaimSpec::default()
    );
}

#[test]
#[verifier(external)]
pub fn test_set_access_modes() {
    let mut persistent_volume_claim_spec = PersistentVolumeClaimSpec::default();
    let access_modes_gen = || {
        let mut access_modes = Vec::new();
        access_modes.push(new_strlit("ReadWriteOnce").to_string());
        access_modes.push(new_strlit("ReadOnlyMany").to_string());
        access_modes
    };
    persistent_volume_claim_spec.set_access_modes(access_modes_gen());
    assert_eq!(
        access_modes_gen()
        .into_iter()
        .map(|a: String| a.into_rust_string())
        .collect::<Vec<_>>(),
        persistent_volume_claim_spec.into_kube().access_modes.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_set_resources() {
    let mut persistent_volume_claim_spec = PersistentVolumeClaimSpec::default();
    let mut resources = ResourceRequirements::default();
    let mut requests = StringMap::new();
    requests.insert(new_strlit("storage").to_string(), new_strlit("1Gi").to_string());
    resources.set_requests(requests);
    persistent_volume_claim_spec.set_resources(resources.clone());
    assert_eq!(
        resources.into_kube(),
        persistent_volume_claim_spec.into_kube().resources.unwrap()
    );
}
#[test]
#[verifier(external)]
pub fn test_clone(){
    let mut persistent_volume_claim_spec = PersistentVolumeClaimSpec::default();
    let mut resources = ResourceRequirements::default();
    let mut requests = StringMap::new();
    requests.insert(new_strlit("storage").to_string(), new_strlit("1Gi").to_string());
    resources.set_requests(requests);
    persistent_volume_claim_spec.set_resources(resources.clone());
    let persistent_volume_claim_spec_clone = persistent_volume_claim_spec.clone();
    assert_eq!(
        resources.into_kube(),
        persistent_volume_claim_spec_clone.into_kube().resources.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_set_storage_class_name() {
    let mut persistent_volume_claim_spec = PersistentVolumeClaimSpec::default();
    persistent_volume_claim_spec.set_storage_class_name(new_strlit("storage_class_name").to_string());
    assert_eq!(
        "storage_class_name".to_string(),
        persistent_volume_claim_spec.into_kube().storage_class_name.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_persistent_volume_claim_spec =
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
        };

    let persistent_volume_claim_spec = PersistentVolumeClaimSpec::from_kube(kube_persistent_volume_claim_spec.clone());
    assert_eq!(
        persistent_volume_claim_spec.into_kube(),
        kube_persistent_volume_claim_spec
    );
}

}
