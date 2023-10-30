// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, label_selector::*, marshal::*, object_meta::*,
    persistent_volume_claim::*, pod_template_spec::*, resource::*, stateful_set::*,
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
    let mut label_selector = LabelSelector::default();
    let mut match_labels = StringMap::new();
    match_labels.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    label_selector.set_match_labels(match_labels);
    let mut stateful_set_spec = StatefulSetSpec::default();
    stateful_set_spec.set_selector(label_selector.clone());
    assert_eq!(
        label_selector.into_kube(),
        stateful_set_spec.into_kube().selector
    );
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let sts_pvc_retention_policy = StatefulSetSpec::from_kube(
        deps_hack::k8s_openapi::api::apps::v1::StatefulSetSpec {
            replicas: Some(1),
            selector: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector {
                match_labels: Some(vec![(
                    "key".to_string(),
                    "value".to_string(),
                )].into_iter().collect()),
                ..Default::default()
            },
            ..Default::default()
        },
    );

    assert_eq!(
        sts_pvc_retention_policy.into_kube(),
        deps_hack::k8s_openapi::api::apps::v1::StatefulSetSpec {
            replicas: Some(1),
            selector: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector {
                match_labels: Some(vec![(
                    "key".to_string(),
                    "value".to_string(),
                )].into_iter().collect()),
                ..Default::default()
            },
            ..Default::default()
        }
    )
}
}
