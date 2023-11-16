// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::daemon_set::*;
use crate::kubernetes_api_objects::exec::label_selector::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::pod_template_spec::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for daemon set
#[test]
#[verifier(external)]
pub fn test_default() {
    let daemon_set = DaemonSet::default();
    assert_eq!(daemon_set.into_kube(), deps_hack::k8s_openapi::api::apps::v1::DaemonSet::default());
}

#[test]
#[verifier(external)]
pub fn test_set_metadata(){
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    let mut daemon_set = DaemonSet::default();
    daemon_set.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), daemon_set.into_kube().metadata);
}

#[test]
#[verifier(external)]
pub fn test_metadata(){
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    let mut daemon_set = DaemonSet::default();
    daemon_set.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), daemon_set.metadata().into_kube());
}

#[test]
#[verifier(external)]
pub fn test_set_sepc() {
    let mut daemon_set = DaemonSet::default();
    let mut daemon_set_spec = DaemonSetSpec::default();
    let mut label_selector = LabelSelector::default();
    let mut match_labels = StringMap::new();
    match_labels.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    label_selector.set_match_labels(match_labels.clone());
    daemon_set_spec.set_selector(label_selector.clone());
    daemon_set.set_spec(daemon_set_spec.clone());
    assert_eq!(daemon_set_spec.into_kube(), daemon_set.into_kube().spec.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_spec() {
    let mut daemon_set = DaemonSet::default();
    let temp = daemon_set.spec();
    if !temp.is_none() {
        panic!("spec should be none");
    }
    let mut daemon_set_spec = DaemonSetSpec::default();
    let mut label_selector = LabelSelector::default();
    let mut match_labels = StringMap::new();
    match_labels.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    label_selector.set_match_labels(match_labels.clone());
    daemon_set_spec.set_selector(label_selector.clone());
    daemon_set.set_spec(daemon_set_spec.clone());
    assert_eq!(daemon_set_spec.into_kube(), daemon_set.spec().unwrap().into_kube());
}

#[test]
#[verifier(external)]
pub fn test_api_resource() {
    let api_resource = DaemonSet::api_resource();
    assert_eq!(api_resource.into_kube().kind, "DaemonSet");
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut daemon_set = DaemonSet::default();
    let mut daemon_set_spec = DaemonSetSpec::default();
    let mut pod_template_spec = PodTemplateSpec::default();
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    pod_template_spec.set_metadata(object_meta.clone());
    daemon_set_spec.set_template(pod_template_spec.clone());
    daemon_set.set_spec(daemon_set_spec.clone());
    let daemon_set_clone = daemon_set.clone();
    assert_eq!(daemon_set.into_kube(), daemon_set_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_daemon_set =
        deps_hack::k8s_openapi::api::apps::v1::DaemonSet {
            metadata: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                name: Some("name".to_string()),
                ..Default::default()
            },
            spec: Some(deps_hack::k8s_openapi::api::apps::v1::DaemonSetSpec {
                selector: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector {
                    match_labels: Some(
                        vec![("key".to_string(), "value".to_string())]
                            .into_iter()
                            .collect(),
                    ),
                    ..Default::default()
                },
                ..Default::default()
            }),
            ..Default::default()
        };

    let daemon_set = DaemonSet::from_kube(kube_daemon_set.clone());
    assert_eq!(
        daemon_set.into_kube(),
        kube_daemon_set
    );
}

#[test]
#[verifier(external)]
pub fn test_marshal() {
    let kube_daemon_set = deps_hack::k8s_openapi::api::apps::v1::DaemonSet {
        metadata: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
            name: Some("name".to_string()),
            ..Default::default()
        },
        spec: Some(deps_hack::k8s_openapi::api::apps::v1::DaemonSetSpec {
            selector: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector {
                match_labels: Some(
                    vec![("key".to_string(), "value".to_string())]
                        .into_iter()
                        .collect(),
                ),
                ..Default::default()
            },
            ..Default::default()
        }),
        ..Default::default()
    };
    let daemon_set = DaemonSet::from_kube(kube_daemon_set.clone());
    assert_eq!(
        kube_daemon_set,
        DaemonSet::unmarshal(daemon_set.marshal()).unwrap().into_kube()
    );
}
}
