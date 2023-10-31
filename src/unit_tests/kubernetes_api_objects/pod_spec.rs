// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::affinity::*;
use crate::kubernetes_api_objects::container::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::pod::*;
use crate::kubernetes_api_objects::resource::*;
use crate::kubernetes_api_objects::toleration::*;
use crate::kubernetes_api_objects::volume::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for pod spec
#[test]
#[verifier(external)]
pub fn test_default() {
    let pod_template_spec = PodSpec::default();
    assert_eq!(pod_template_spec.into_kube(), deps_hack::k8s_openapi::api::core::v1::PodSpec::default());
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut pod_spec = PodSpec::default();
    let mut container = Container::default();
    container.set_name(new_strlit("name").to_string());
    pod_spec.set_containers(vec![container.clone()]);
    let pod_spec_clone = pod_spec.clone();
    assert_eq!(pod_spec.into_kube(), pod_spec_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_set_affinity() {
    let mut pod_spec = PodSpec::default();
    let affinity = Affinity::from_kube(deps_hack::k8s_openapi::api::core::v1::Affinity::default());
    pod_spec.set_affinity(affinity);
    assert_eq!(deps_hack::k8s_openapi::api::core::v1::Affinity::default(), pod_spec.into_kube().affinity.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_overwrite_affinity() {
    let mut pod_spec = PodSpec::default();
    let affinity = Affinity::from_kube(deps_hack::k8s_openapi::api::core::v1::Affinity::default());
    pod_spec.overwrite_affinity(Some(affinity));
    assert_eq!(deps_hack::k8s_openapi::api::core::v1::Affinity::default(), pod_spec.clone().into_kube().affinity.unwrap());
    pod_spec.overwrite_affinity(None);
    assert_eq!(None, pod_spec.into_kube().affinity);
}

#[test]
#[verifier(external)]
pub fn test_set_containers() {
    let mut pod_spec = PodSpec::default();
    let mut container = Container::default();
    let mut container2 = Container::default();
    container.set_name(new_strlit("name").to_string());
    container2.set_name(new_strlit("name2").to_string());
    pod_spec.set_containers(vec![container.clone(), container2.clone()]);
    assert_eq!(vec![container.into_kube(), container2.into_kube()], pod_spec.into_kube().containers);
}

#[test]
#[verifier(external)]
pub fn test_set_volumes() {
    let mut pod_spec = PodSpec::default();
    let mut volume = Volume::default();
    let mut volume2 = Volume::default();
    volume.set_name(new_strlit("name").to_string());
    volume2.set_name(new_strlit("name2").to_string());
    pod_spec.set_volumes(vec![volume.clone(), volume2.clone()]);
    assert_eq!(vec![volume.into_kube(), volume2.into_kube()], pod_spec.into_kube().volumes.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_init_containers() {
    let mut pod_spec = PodSpec::default();
    let mut container = Container::default();
    let mut container2 = Container::default();
    container.set_name(new_strlit("name").to_string());
    container2.set_name(new_strlit("name2").to_string());
    pod_spec.set_init_containers(vec![container.clone(), container2.clone()]);
    assert_eq!(vec![container.into_kube(), container2.into_kube()], pod_spec.into_kube().init_containers.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_service_account_name() {
    let mut pod_spec = PodSpec::default();
    pod_spec.set_service_account_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), pod_spec.into_kube().service_account_name.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_tolerations() {
    let mut pod_spec = PodSpec::default();
    let toleration = Toleration::from_kube(deps_hack::k8s_openapi::api::core::v1::Toleration::default());
    pod_spec.set_tolerations(vec![toleration]);
    assert_eq!(vec![deps_hack::k8s_openapi::api::core::v1::Toleration::default()], pod_spec.into_kube().tolerations.unwrap());
}

#[test]
#[verifier(external)]
pub fn overwrite_tolerations() {
    let mut pod_spec = PodSpec::default();
    let toleration = Toleration::from_kube(deps_hack::k8s_openapi::api::core::v1::Toleration::default());
    pod_spec.overwrite_tolerations(Some(vec![toleration]));
    assert_eq!(vec![deps_hack::k8s_openapi::api::core::v1::Toleration::default()], pod_spec.clone().into_kube().tolerations.unwrap());
    pod_spec.overwrite_tolerations(None);
    assert_eq!(None, pod_spec.into_kube().tolerations);
}

#[test]
#[verifier(external)]
pub fn test_set_node_selector() {
    let mut pod_spec = PodSpec::default();
    let mut node_selector = StringMap::new();
    node_selector.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    pod_spec.set_node_selector(node_selector.clone());
    assert_eq!(node_selector.into_rust_map(), pod_spec.into_kube().node_selector.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_pod_spec =
        deps_hack::k8s_openapi::api::core::v1::PodSpec {
            containers:
                vec![
                    deps_hack::k8s_openapi::api::core::v1::Container {
                        name: "name".to_string(),
                        ..Default::default()
                    },
                    deps_hack::k8s_openapi::api::core::v1::Container {
                        name: "name_2".to_string(),
                        ..Default::default()
                    },
                ],
            volumes: Some(
                vec![
                    deps_hack::k8s_openapi::api::core::v1::Volume {
                        name: "name".to_string(),
                        ..Default::default()
                    },
                    deps_hack::k8s_openapi::api::core::v1::Volume {
                        name: "name_2".to_string(),
                        ..Default::default()
                    },
                ],
            ),

            init_containers: Some(
                vec![
                    deps_hack::k8s_openapi::api::core::v1::Container {
                        name: "name".to_string(),
                        ..Default::default()
                    },
                    deps_hack::k8s_openapi::api::core::v1::Container {
                        name: "name_2".to_string(),
                        ..Default::default()
                    },
                ],
            ),
            service_account_name: Some("name".to_string()),
            tolerations: Some(
                vec![
                    deps_hack::k8s_openapi::api::core::v1::Toleration {
                        key: Some("key".to_string()),
                        ..Default::default()
                    },
                    deps_hack::k8s_openapi::api::core::v1::Toleration {
                        key: Some("key_2".to_string()),
                        ..Default::default()
                    },
                ],
            ),
            node_selector: Some(
                vec![
                    (
                        "key".to_string(),
                        "value".to_string(),
                    ),
                    (
                        "key_2".to_string(),
                        "value_2".to_string(),
                    ),
                ]
                .into_iter()
                .collect(),
            ),
            affinity: Some(
                deps_hack::k8s_openapi::api::core::v1::Affinity {
                    node_affinity: Some(
                        deps_hack::k8s_openapi::api::core::v1::NodeAffinity {
                            required_during_scheduling_ignored_during_execution: Some(
                                deps_hack::k8s_openapi::api::core::v1::NodeSelector {
                                    node_selector_terms:
                                        vec![
                                            deps_hack::k8s_openapi::api::core::v1::NodeSelectorTerm {
                                                match_expressions: Some(
                                                    vec![
                                                        deps_hack::k8s_openapi::api::core::v1::NodeSelectorRequirement {
                                                            key: "key".to_string(),
                                                            operator: "operator".to_string(),
                                                            values: Some(
                                                                vec![
                                                                    "value".to_string(),
                                                                    "value_2".to_string(),
                                                                ],
                                                            ),
                                                            ..Default::default()
                                                        },
                                                        deps_hack::k8s_openapi::api::core::v1::NodeSelectorRequirement {
                                                            key: "key_2".to_string(),
                                                            operator: "operator_2".to_string(),
                                                            values: Some(
                                                                vec![
                                                                    "value".to_string(),
                                                                    "value_2".to_string(),
                                                                ],
                                                            ),
                                                            ..Default::default()
                                                        },
                                                    ],
                                                ),
                                                ..Default::default()
                                            },
                                            deps_hack::k8s_openapi::api::core::v1::NodeSelectorTerm {
                                                match_fields: Some(
                                                    vec![
                                                        deps_hack::k8s_openapi::api::core::v1::NodeSelectorRequirement {
                                                            key: "key".to_string(),
                                                            operator: "operator".to_string(),
                                                            values: Some(
                                                                vec![
                                                                    "value".to_string(),
                                                                    "value_2".to_string(),
                                                                ],
                                                            ),
                                                            ..Default::default()
                                                        },
                                                        deps_hack::k8s_openapi::api::core::v1::NodeSelectorRequirement {
                                                            key: "key_2".to_string(),
                                                            operator: "operator_2".to_string(),
                                                            values: Some(
                                                                vec![
                                                                    "value".to_string(),
                                                                    "value_2".to_string(),
                                                                ],
                                                            ),
                                                            ..Default::default()
                                                        },
                                                    ],
                                                ),
                                                ..Default::default()
                                            },
                                        ],

                                    ..Default::default()
                                },
                            ),
                            ..Default::default()
                        },
                    ),
                    ..Default::default()
                },
            ),
            ..Default::default()
        };

    let pod_spec = PodSpec::from_kube(kube_pod_spec.clone());
    assert_eq!(
        pod_spec.into_kube(),
        kube_pod_spec
    );
}
}
