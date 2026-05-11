// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, label_selector::*, object_meta::*, persistent_volume_claim::*,
    pod_template_spec::*, resource::*, stateful_set::*,
};
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

#[test]
pub fn test_default() {
    let stateful_set_pvc_retention_policy =
        StatefulSetPersistentVolumeClaimRetentionPolicy::default();
    assert_eq!(
        stateful_set_pvc_retention_policy.into_kube(),
        k8s_openapi::api::apps::v1::StatefulSetPersistentVolumeClaimRetentionPolicy::default()
    );
}

#[test]
pub fn test_set_when_deleted() {
    let mut stateful_set_pvc_retention_policy =
        StatefulSetPersistentVolumeClaimRetentionPolicy::default();
    stateful_set_pvc_retention_policy.set_when_deleted("Retain".to_string());
    assert_eq!(
        "Retain".to_string(),
        stateful_set_pvc_retention_policy
            .into_kube()
            .when_deleted
            .unwrap()
    );
}

#[test]
pub fn test_set_when_scaled() {
    let mut stateful_set_pvc_retention_policy =
        StatefulSetPersistentVolumeClaimRetentionPolicy::default();
    stateful_set_pvc_retention_policy.set_when_scaled("Delete".to_string());
    assert_eq!(
        "Delete".to_string(),
        stateful_set_pvc_retention_policy
            .into_kube()
            .when_scaled
            .unwrap()
    );
}

#[test]
pub fn test_clone() {
    let mut stateful_set_pvc_retention_policy =
        StatefulSetPersistentVolumeClaimRetentionPolicy::default();
    stateful_set_pvc_retention_policy.set_when_deleted("Retain".to_string());
    stateful_set_pvc_retention_policy.set_when_scaled("Delete".to_string());
    let cloned_stateful_set_pvc_retention_policy = stateful_set_pvc_retention_policy.clone();
    assert_eq!(
        stateful_set_pvc_retention_policy.into_kube(),
        cloned_stateful_set_pvc_retention_policy.into_kube()
    );
}

#[test]
pub fn test_kube() {
    let kube_stateful_set_pvc_retention_policy =
        k8s_openapi::api::apps::v1::StatefulSetPersistentVolumeClaimRetentionPolicy {
            when_deleted: Some("Retain".to_string()),
            when_scaled: Some("Delete".to_string()),
            ..Default::default()
        };

    let stateful_set_pvc_retention_policy =
        StatefulSetPersistentVolumeClaimRetentionPolicy::from_kube(
            kube_stateful_set_pvc_retention_policy.clone(),
        );

    assert_eq!(
        stateful_set_pvc_retention_policy.into_kube(),
        kube_stateful_set_pvc_retention_policy
    );
}
