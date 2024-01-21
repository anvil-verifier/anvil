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
// Tests for stateful set
#[test]
#[verifier(external)]
pub fn test_default() {
    let stateful_set = StatefulSet::default();
    assert_eq!(
        stateful_set.into_kube(),
        deps_hack::k8s_openapi::api::apps::v1::StatefulSet::default()
    );
}

#[test]
#[verifier(external)]
pub fn test_set_metadata() {
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    object_meta.set_namespace(new_strlit("namespace").to_string());
    let mut stateful_set = StatefulSet::default();
    stateful_set.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), stateful_set.into_kube().metadata);
}

#[test]
#[verifier(external)]
pub fn test_metadata() {
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    object_meta.set_namespace(new_strlit("namespace").to_string());
    let mut stateful_set = StatefulSet::default();
    stateful_set.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), stateful_set.metadata().into_kube());
}

#[test]
#[verifier(external)]
pub fn test_set_spec() {
    let mut stateful_set_spec = StatefulSetSpec::default();
    stateful_set_spec.set_replicas(1);
    let mut stateful_set = StatefulSet::default();
    stateful_set.set_spec(stateful_set_spec.clone());
    assert_eq!(stateful_set_spec.into_kube(), stateful_set.into_kube().spec.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_spec() {
    let mut stateful_set_spec = StatefulSetSpec::default();
    stateful_set_spec.set_replicas(1024);
    let mut stateful_set = StatefulSet::default();
    let temp = stateful_set.spec();
    if !temp.is_none() {
        panic!("StatefulSet spec should be None, but it's not.");
    }
    stateful_set.set_spec(stateful_set_spec.clone());
    assert_eq!(stateful_set_spec.into_kube(), stateful_set.spec().unwrap().into_kube());
}

#[test]
#[verifier(external)]
pub fn test_api_resource() {
    let api_resource = StatefulSet::api_resource();
    assert_eq!(api_resource.into_kube().kind, "StatefulSet");
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    object_meta.set_namespace(new_strlit("namespace").to_string());
    let mut stateful_set = StatefulSet::default();
    stateful_set.set_metadata(object_meta.clone());
    let mut stateful_set_spec = StatefulSetSpec::default();
    stateful_set_spec.set_replicas(1024);
    stateful_set.set_spec(stateful_set_spec.clone());
    let cloned_stateful_set = stateful_set.clone();
    assert_eq!(
        stateful_set.into_kube(),
        cloned_stateful_set.into_kube()
    );
}

#[test]
#[verifier(external)]
pub fn test_status() {
    let stateful_set = StatefulSet::default();
    let temp = stateful_set.status();
    if !temp.is_none() {
        panic!("StatefulSet status should be None, but it's not.");
    }
    let stateful_set_status = StatefulSetStatus::from_kube(deps_hack::k8s_openapi::api::apps::v1::StatefulSetStatus {
        replicas: 1024,
        ready_replicas: Some(1024),
        ..Default::default()
    });
    let stateful_set = StatefulSet::from_kube(deps_hack::k8s_openapi::api::apps::v1::StatefulSet {
        status: Some(deps_hack::k8s_openapi::api::apps::v1::StatefulSetStatus {
            replicas: 1024,
            ready_replicas: Some(1024),
            ..Default::default()
        }),
        ..Default::default()
    });
    assert_eq!(stateful_set_status.into_kube(), stateful_set.status().unwrap().into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_stateful_set =
        deps_hack::k8s_openapi::api::apps::v1::StatefulSet {
            metadata: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                name: Some("name".to_string()),
                namespace: Some("namespace".to_string()),
                ..Default::default()
            },
            spec: Some(deps_hack::k8s_openapi::api::apps::v1::StatefulSetSpec {
                replicas: Some(1),
                selector: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector {
                    match_labels: Some(vec![(
                        "key".to_string(),
                        "value".to_string(),
                    )].into_iter().collect()),
                    ..Default::default()
                },
                template: deps_hack::k8s_openapi::api::core::v1::PodTemplateSpec {
                    metadata: Some(deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                        name: Some("name".to_string()),
                        namespace: Some("namespace".to_string()),
                        ..Default::default()
                    }),
                    spec: Some(deps_hack::k8s_openapi::api::core::v1::PodSpec {
                        containers: vec![
                            deps_hack::k8s_openapi::api::core::v1::Container {
                                name: "name".to_string(),
                                image: Some("image".to_string()),
                                ..Default::default()
                            },
                        ],
                        ..Default::default()
                    }),
                    ..Default::default()
                },
                ..Default::default()
            }),
            ..Default::default()
        };

    let stateful_set = StatefulSet::from_kube(kube_stateful_set.clone());

    assert_eq!(
        stateful_set.into_kube(),
        kube_stateful_set
    );
}

#[verifier(external)]
pub fn test_marshal() {
    let kube_stateful_set =
        deps_hack::k8s_openapi::api::apps::v1::StatefulSet {
            metadata: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                name: Some("name".to_string()),
                namespace: Some("namespace".to_string()),
                ..Default::default()
            },
            spec: Some(deps_hack::k8s_openapi::api::apps::v1::StatefulSetSpec {
                replicas: Some(1),
                selector: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector {
                    match_labels: Some(vec![(
                        "key".to_string(),
                        "value".to_string(),
                    )].into_iter().collect()),
                    ..Default::default()
                },
                template: deps_hack::k8s_openapi::api::core::v1::PodTemplateSpec {
                    metadata: Some(deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                        name: Some("name".to_string()),
                        namespace: Some("namespace".to_string()),
                        ..Default::default()
                    }),
                    spec: Some(deps_hack::k8s_openapi::api::core::v1::PodSpec {
                        containers: vec![
                            deps_hack::k8s_openapi::api::core::v1::Container {
                                name: "name".to_string(),
                                image: Some("image".to_string()),
                                ..Default::default()
                            },
                        ],
                        ..Default::default()
                    }),
                    ..Default::default()
                },
                ..Default::default()
            }),
            ..Default::default()
        };

    let stateful_set = StatefulSet::from_kube(kube_stateful_set.clone());

    assert_eq!(
        kube_stateful_set,
        StatefulSet::unmarshal(stateful_set.marshal())
            .unwrap()
            .into_kube()
    );
}
}
