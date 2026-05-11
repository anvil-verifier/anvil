// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::container::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::pod::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

#[test]
pub fn test_default() {
    let pod = Pod::default();
    assert_eq!(
        pod.into_kube(),
        k8s_openapi::api::core::v1::Pod::default()
    );
}

#[test]
pub fn test_metadata() {
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name("name".to_string());

    let mut pod = Pod::default();
    pod.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), pod.metadata().into_kube());
}

#[test]
pub fn test_spec() {
    let mut pod_spec = PodSpec::default();
    let mut container = Container::default();
    container.set_name("name".to_string());
    pod_spec.set_containers(vec![container.clone()]);
    let mut pod = Pod::default();
    pod.set_spec(pod_spec.clone());
    assert_eq!(pod_spec.into_kube(), pod.spec().unwrap().into_kube());
}

#[test]
pub fn test_set_metadata() {
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name("name".to_string());

    let mut pod = Pod::default();
    pod.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), pod.into_kube().metadata);
}

#[test]
pub fn test_set_spec() {
    let mut pod_spec = PodSpec::default();
    let mut container = Container::default();
    container.set_name("name".to_string());
    pod_spec.set_containers(vec![container.clone()]);
    let mut pod = Pod::default();
    pod.set_spec(pod_spec.clone());
    assert_eq!(pod_spec.into_kube(), pod.into_kube().spec.unwrap());
}

#[test]
pub fn test_api_resource() {
    let api_resource = Pod::api_resource();
    assert_eq!(api_resource.into_kube().kind, "Pod");
}

#[test]
pub fn test_kube() {
    let kube_pod = k8s_openapi::api::core::v1::Pod {
        metadata: k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
            name: Some("name".to_string()),
            ..Default::default()
        },
        spec: Some(k8s_openapi::api::core::v1::PodSpec {
            containers: vec![k8s_openapi::api::core::v1::Container {
                name: "name".to_string(),
                ..Default::default()
            }],
            ..Default::default()
        }),
        ..Default::default()
    };

    let pod = Pod::from_kube(kube_pod.clone());

    assert_eq!(pod.into_kube(), kube_pod);
}

#[test]
pub fn test_marshal() {
    let kube_pod = k8s_openapi::api::core::v1::Pod {
        metadata: k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
            name: Some("name".to_string()),
            ..Default::default()
        },
        spec: Some(k8s_openapi::api::core::v1::PodSpec {
            containers: vec![k8s_openapi::api::core::v1::Container {
                name: "name".to_string(),
                ..Default::default()
            }],
            ..Default::default()
        }),
        ..Default::default()
    };

    let pod = Pod::from_kube(kube_pod.clone());

    assert_eq!(kube_pod, Pod::unmarshal(pod.marshal()).unwrap().into_kube());
}
