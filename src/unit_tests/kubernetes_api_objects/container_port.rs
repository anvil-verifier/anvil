// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::container::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::resource_requirements::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

// Tests for ports(ContainerPort)
#[test]
#[verifier(external)]
pub fn test_default() {
    let container_port = ContainerPort::default();
    assert_eq!(container_port.into_kube(), deps_hack::k8s_openapi::api::core::v1::ContainerPort::default());
}


#[test]
#[verifier(external)]
pub fn test_set_container_port() {
    let mut container_port = ContainerPort::default();
    container_port.set_container_port(8080);
    assert_eq!(8080, container_port.into_kube().container_port);
}

#[test]
#[verifier(external)]
pub fn test_set_name() {
    let mut container_port = ContainerPort::default();
    container_port.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), container_port.into_kube().name.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_name() {
    let mut container_port = ContainerPort::default();
    let temp = container_port.name();
    if !temp.is_none() {
        panic!("name should be none");
    }
    container_port.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), container_port.name().unwrap().into_rust_string());
}

#[test]
#[verifier(external)]
pub fn test_container_port() {
    let mut container_port = ContainerPort::default();
    container_port.set_container_port(8080);
    assert_eq!(8080, container_port.container_port());
}

#[test]
#[verifier(external)]
pub fn test_protocol() {
    let container_port = ContainerPort::default();
    let temp = container_port.protocol();
    if !temp.is_none() {
        panic!("protocol should be none");
    }
    let container_port = ContainerPort::from_kube(deps_hack::k8s_openapi::api::core::v1::ContainerPort {
        container_port: 8080,
        host_ip: Some("host_ip".to_string()),
        host_port: Some(8080),
        name: Some("name".to_string()),
        protocol: Some("protocol".to_string()),
        ..Default::default()
    });
    assert_eq!("protocol".to_string(), container_port.protocol().unwrap().into_rust_string());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_container_port = deps_hack::k8s_openapi::api::core::v1::ContainerPort {
        container_port: 8080,
        host_ip: Some("host_ip".to_string()),
        host_port: Some(8080),
        name: Some("name".to_string()),
        ..Default::default()
    };

    let container_port = ContainerPort::from_kube(kube_container_port.clone());

    assert_eq!(container_port.into_kube(),
                kube_container_port);
}
}
