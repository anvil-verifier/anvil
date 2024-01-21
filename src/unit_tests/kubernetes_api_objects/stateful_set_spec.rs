// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, label_selector::*, object_meta::*, persistent_volume_claim::*,
    pod_template_spec::*, resource::*, stateful_set::*,
};
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for stateful set spec
#[test]
#[verifier(external)]
pub fn test_default() {
    let stateful_set_spec = StatefulSetSpec::default();
    assert_eq!(
        stateful_set_spec.into_kube(),
        deps_hack::k8s_openapi::api::apps::v1::StatefulSetSpec::default()
    );
}

#[test]
#[verifier(external)]
pub fn test_set_replicas() {
    let mut stateful_set_spec = StatefulSetSpec::default();
    stateful_set_spec.set_replicas(1);
    assert_eq!(1, stateful_set_spec.into_kube().replicas.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_selector() {
    let mut stateful_set_spec = StatefulSetSpec::default();
    let mut label_selector = LabelSelector::default();
    let mut match_labels = StringMap::new();
    match_labels.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    label_selector.set_match_labels(match_labels);
    stateful_set_spec.set_selector(label_selector.clone());
    assert_eq!(
        label_selector.into_kube(),
        stateful_set_spec.into_kube().selector
    );
}

#[test]
#[verifier(external)]
pub fn test_set_service_name() {
    let mut stateful_set_spec = StatefulSetSpec::default();
    stateful_set_spec.set_service_name(new_strlit("name").to_string());
    assert_eq!(
        "name".to_string(),
        stateful_set_spec.into_kube().service_name
    );
}

#[test]
#[verifier(external)]
pub fn test_set_template() {
    let mut stateful_set_spec = StatefulSetSpec::default();
    let mut pod_template_spec = PodTemplateSpec::default();
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    pod_template_spec.set_metadata(object_meta);
    stateful_set_spec.set_template(pod_template_spec.clone());
    assert_eq!(
        pod_template_spec.into_kube(),
        stateful_set_spec.into_kube().template
    );
}

#[test]
#[verifier(external)]
pub fn test_set_volume_claim_templates() {
    let mut stateful_set_spec = StatefulSetSpec::default();
    let volume_claim_templates_gen = || {
        let mut volume_claim_templates = Vec::new();
        let mut persistent_volume_claim = PersistentVolumeClaim::default();
        let mut object_meta = ObjectMeta::default();
        object_meta.set_name(new_strlit("name").to_string());
        persistent_volume_claim.set_metadata(object_meta);
        volume_claim_templates.push(persistent_volume_claim);
        volume_claim_templates
    };
    stateful_set_spec.set_volume_claim_templates(volume_claim_templates_gen());
    assert_eq!(
        volume_claim_templates_gen()
            .into_iter()
            .map(|p: PersistentVolumeClaim| p.into_kube())
            .collect::<Vec<_>>(),
        stateful_set_spec
            .into_kube()
            .volume_claim_templates
            .unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_set_pod_management_policy() {
    let mut stateful_set_spec = StatefulSetSpec::default();
    stateful_set_spec.set_pod_management_policy(new_strlit("policy").to_string());
    assert_eq!(
        "policy".to_string(),
        stateful_set_spec.into_kube().pod_management_policy.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_set_pvc_retention_policy() {
    let mut stateful_set_spec = StatefulSetSpec::default();
    let mut pvc_retention_policy = StatefulSetPersistentVolumeClaimRetentionPolicy::default();
    pvc_retention_policy.set_when_deleted(new_strlit("Delete").to_string());
    pvc_retention_policy.set_when_scaled(new_strlit("Retain").to_string());
    stateful_set_spec.set_pvc_retention_policy(pvc_retention_policy.clone());
    assert_eq!(
        pvc_retention_policy.into_kube(),
        stateful_set_spec.into_kube().persistent_volume_claim_retention_policy.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_overwrite_pvc_retention_policy() {
    let mut stateful_set_spec = StatefulSetSpec::default();
    let mut pvc_retention_policy = StatefulSetPersistentVolumeClaimRetentionPolicy::default();
    pvc_retention_policy.set_when_deleted(new_strlit("Delete").to_string());
    pvc_retention_policy.set_when_scaled(new_strlit("Retain").to_string());
    stateful_set_spec.overwrite_pvc_retention_policy(Some(pvc_retention_policy.clone()));
    assert_eq!(
        pvc_retention_policy.into_kube(),
        stateful_set_spec.into_kube().persistent_volume_claim_retention_policy.unwrap()
    );
    let mut stateful_set_spec_2 = StatefulSetSpec::default();
    let pvc_retention_policy_2 = None;
    stateful_set_spec_2.overwrite_pvc_retention_policy(pvc_retention_policy_2);
    assert_eq!(
        None,
        stateful_set_spec_2.into_kube().persistent_volume_claim_retention_policy
    );
}

#[test]
#[verifier(external)]
pub fn test_replicas() {
    let mut stateful_set_spec = StatefulSetSpec::default();
    let temp = stateful_set_spec.replicas();
    if !temp.is_none() {
        panic!("StatefulSet replicas should be None, but it's not.");
    }
    stateful_set_spec.set_replicas(1024);
    assert_eq!(1024, stateful_set_spec.replicas().unwrap());
}

#[test]
#[verifier(external)]
pub fn test_template() {
    let mut stateful_set_spec = StatefulSetSpec::default();
    let mut pod_template_spec = PodTemplateSpec::default();
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    pod_template_spec.set_metadata(object_meta);
    stateful_set_spec.set_template(pod_template_spec.clone());
    assert_eq!(
        pod_template_spec.into_kube(),
        stateful_set_spec.template().into_kube()
    );
}

#[test]
#[verifier(external)]
pub fn test_persistent_volume_claim_retention_policy() {
    let mut stateful_set_spec = StatefulSetSpec::default();
    let temp = stateful_set_spec.persistent_volume_claim_retention_policy();
    if !temp.is_none() {
        panic!("StatefulSet persistent_volume_claim_retention_policy should be None, but it's not.");
    }
    let mut pvc_retention_policy = StatefulSetPersistentVolumeClaimRetentionPolicy::default();
    pvc_retention_policy.set_when_deleted(new_strlit("Delete").to_string());
    pvc_retention_policy.set_when_scaled(new_strlit("Retain").to_string());
    stateful_set_spec.set_pvc_retention_policy(pvc_retention_policy.clone());
    assert_eq!(
        pvc_retention_policy.into_kube(),
        stateful_set_spec.persistent_volume_claim_retention_policy().unwrap().into_kube()
    );
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut stateful_set_spec = StatefulSetSpec::default();
    let mut pod_template_spec = PodTemplateSpec::default();
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    pod_template_spec.set_metadata(object_meta);
    stateful_set_spec.set_template(pod_template_spec.clone());
    let mut pvc_retention_policy = StatefulSetPersistentVolumeClaimRetentionPolicy::default();
    pvc_retention_policy.set_when_deleted(new_strlit("Delete").to_string());
    pvc_retention_policy.set_when_scaled(new_strlit("Retain").to_string());
    stateful_set_spec.set_pvc_retention_policy(pvc_retention_policy.clone());
    let stateful_set_spec_clone = stateful_set_spec.clone();
    assert_eq!(
        stateful_set_spec.into_kube(),
        stateful_set_spec_clone.into_kube()
    );
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_sts_spec =
        deps_hack::k8s_openapi::api::apps::v1::StatefulSetSpec {
            replicas: Some(1),
            selector: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector {
                match_labels: Some(vec![(
                    "key".to_string(),
                    "value".to_string(),
                )].into_iter().collect()),
                ..Default::default()
            },
            service_name: "name".to_string(),
            template: deps_hack::k8s_openapi::api::core::v1::PodTemplateSpec {
                metadata: Some(deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                    name: Some("name".to_string()),
                    ..Default::default()
                }),
                ..Default::default()
            },
            volume_claim_templates: Some(vec![deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim {
                metadata: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                    name: Some("name".to_string()),
                    ..Default::default()
                },
                ..Default::default()
            }]),
            pod_management_policy: Some("policy".to_string()),
            persistent_volume_claim_retention_policy: Some(
                deps_hack::k8s_openapi::api::apps::v1::StatefulSetPersistentVolumeClaimRetentionPolicy {
                    when_deleted: Some("Delete".to_string()),
                    when_scaled: Some("Retain".to_string()),
                }
            ),
            ..Default::default()
        };

    let sts_spec = StatefulSetSpec::from_kube(kube_sts_spec.clone());
    assert_eq!(
        sts_spec.into_kube(),
        kube_sts_spec
    );
}
}
