// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::service::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

#[test]
pub fn test_default() {
    let service = Service::default();
    assert_eq!(
        service.into_kube(),
        k8s_openapi::api::core::v1::Service::default()
    );
}

#[test]
pub fn test_set_metadata() {
    let mut service = Service::default();
    let mut metadata = ObjectMeta::default();
    metadata.set_name("name".to_string());
    service.set_metadata(metadata.clone());
    assert_eq!(metadata.into_kube(), service.into_kube().metadata);
}

#[test]
pub fn test_metadata() {
    let mut service = Service::default();
    let mut metadata = ObjectMeta::default();
    metadata.set_name("name".to_string());
    service.set_metadata(metadata.clone());
    assert_eq!(metadata.into_kube(), service.metadata().into_kube());
}

#[test]
pub fn test_set_spec() {
    let mut service = Service::default();
    let mut spec = ServiceSpec::default();
    spec.set_cluster_ip("ip".to_string());
    service.set_spec(spec.clone());
    assert_eq!(spec.into_kube(), service.into_kube().spec.unwrap());
}

#[test]
pub fn test_spec() {
    let mut service = Service::default();
    let mut spec = ServiceSpec::default();
    // @TODO: How to test None
    // assert_eq!(None, service.spec());
    spec.set_cluster_ip("ip".to_string());
    service.set_spec(spec.clone());
    assert_eq!(spec.into_kube(), service.spec().unwrap().into_kube());
}

#[test]
pub fn test_api_resource() {
    let api_resource = Service::api_resource();
    assert_eq!(api_resource.into_kube().kind, "Service");
}

#[test]
pub fn test_clone() {
    let mut service = Service::default();
    let mut metadata = ObjectMeta::default();
    metadata.set_name("name".to_string());
    service.set_metadata(metadata.clone());
    let mut spec = ServiceSpec::default();
    spec.set_cluster_ip("ip".to_string());
    service.set_spec(spec.clone());
    let service_clone = service.clone();
    assert_eq!(service.into_kube(), service_clone.into_kube());
}

#[test]
pub fn test_kube() {
    let kube_service = k8s_openapi::api::core::v1::Service {
        metadata: k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
            name: Some("name".to_string()),
            ..Default::default()
        },
        spec: Some(k8s_openapi::api::core::v1::ServiceSpec {
            cluster_ip: Some("ip".to_string()),
            ..Default::default()
        }),
        ..Default::default()
    };

    let service = Service::from_kube(kube_service.clone());

    assert_eq!(service.into_kube(), kube_service);
}

#[test]
pub fn test_marshal() {
    let kube_service = k8s_openapi::api::core::v1::Service {
        metadata: k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
            name: Some("name".to_string()),
            ..Default::default()
        },
        spec: Some(k8s_openapi::api::core::v1::ServiceSpec {
            cluster_ip: Some("ip".to_string()),
            ..Default::default()
        }),
        ..Default::default()
    };

    let service = Service::from_kube(kube_service.clone());

    assert_eq!(
        kube_service,
        Service::unmarshal(service.marshal()).unwrap().into_kube()
    );
}
