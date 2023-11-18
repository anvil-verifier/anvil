// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::service::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for service spec
#[test]
#[verifier(external)]
pub fn test_default() {
    let service_spec = ServiceSpec::default();
    assert_eq!(service_spec.into_kube(), deps_hack::k8s_openapi::api::core::v1::ServiceSpec::default());
}

#[test]
#[verifier(external)]
pub fn test_set_cluster_ip() {
    let mut service_spec = ServiceSpec::default();
    service_spec.set_cluster_ip(new_strlit("ip").to_string());
    assert_eq!("ip".to_string(), service_spec.into_kube().cluster_ip.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_ports() {
    let mut service_spec = ServiceSpec::default();
    let ports_gen = || {
        let mut ports = Vec::new();
        let mut port = ServicePort::default();
        let mut port_2 = ServicePort::default();
        port.set_port(1);
        port.set_app_protocol(new_strlit("http").to_string());
        port_2.set_port(2048);
        port_2.set_app_protocol(new_strlit("tcp").to_string());
        ports.push(port);
        ports
    };
    service_spec.set_ports(ports_gen());
    assert_eq!(ports_gen()
                .into_iter()
                .map(|p: ServicePort| p
                .into_kube()).collect::<Vec<_>>(),
        service_spec.into_kube().ports.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_ports() {
    let mut service_spec = ServiceSpec::default();
    let ports_gen = || {
        let mut ports = Vec::new();
        let mut port = ServicePort::default();
        let mut port_2 = ServicePort::default();
        port.set_port(1);
        port.set_app_protocol(new_strlit("http").to_string());
        port_2.set_port(2048);
        port_2.set_app_protocol(new_strlit("tcp").to_string());
        ports.push(port);
        ports
    };
    service_spec.set_ports(ports_gen());
    assert_eq!(ports_gen()
                .into_iter()
                .map(|p: ServicePort| p.into_kube())
                .collect::<Vec<_>>(),
                service_spec.ports().unwrap()
                .into_iter()
                .map(|p: ServicePort| p.into_kube())
                .collect::<Vec<_>>()
            );
}

#[test]
#[verifier(external)]
pub fn test_set_selector() {
    let mut service_spec = ServiceSpec::default();
    let mut selector = StringMap::new();
    selector.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    service_spec.set_selector(selector.clone());
    assert_eq!(selector.into_rust_map(), service_spec.into_kube().selector.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_selector() {
    let mut service_spec = ServiceSpec::default();
    let mut selector = StringMap::new();
    selector.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    service_spec.set_selector(selector.clone());
    assert_eq!(selector.into_rust_map(), service_spec.selector().unwrap().into_rust_map());
}

#[test]
#[verifier(external)]
pub fn test_set_publish_not_ready_addresses() {
    let mut service_spec = ServiceSpec::default();
    service_spec.set_publish_not_ready_addresses(true);
    assert_eq!(true, service_spec.into_kube().publish_not_ready_addresses.unwrap());

    let mut service_spec_2 = ServiceSpec::default();
    service_spec_2.set_publish_not_ready_addresses(false);
    assert_eq!(false, service_spec_2.into_kube().publish_not_ready_addresses.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_unset_publish_not_ready_addresses() {
    let mut service_spec = ServiceSpec::default();
    service_spec.set_publish_not_ready_addresses(true);
    service_spec.unset_publish_not_ready_addresses();
    assert_eq!(None, service_spec.into_kube().publish_not_ready_addresses);
}


#[test]
#[verifier(external)]
pub fn test_publish_not_ready_addresses() {
    let mut service_spec = ServiceSpec::default();
    assert_eq!(None, service_spec.publish_not_ready_addresses());
    service_spec.set_publish_not_ready_addresses(true);
    assert_eq!(true, service_spec.publish_not_ready_addresses().unwrap());

    let mut service_spec_2 = ServiceSpec::default();
    service_spec_2.set_publish_not_ready_addresses(false);
    assert_eq!(false, service_spec_2.publish_not_ready_addresses().unwrap());
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut service_spec = ServiceSpec::default();
    service_spec.set_cluster_ip(new_strlit("ip").to_string());
    let ports_gen = || {
        let mut ports = Vec::new();
        let mut port = ServicePort::default();
        let mut port_2 = ServicePort::default();
        port.set_port(1);
        port.set_app_protocol(new_strlit("http").to_string());
        port_2.set_port(2048);
        port_2.set_app_protocol(new_strlit("tcp").to_string());
        ports.push(port);
        ports
    };
    service_spec.set_ports(ports_gen());
    let mut selector = StringMap::new();
    selector.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    service_spec.set_selector(selector.clone());
    service_spec.set_publish_not_ready_addresses(true);
    let cloned_service_spec = service_spec.clone();
    assert_eq!(
        service_spec.into_kube(),
        cloned_service_spec.into_kube()
    );
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_service_spec =
        deps_hack::k8s_openapi::api::core::v1::ServiceSpec {
            cluster_ip: Some("ip".to_string()),
            ports: Some(vec![
                deps_hack::k8s_openapi::api::core::v1::ServicePort {
                    port: 1,
                    app_protocol: Some("http".to_string()),
                    ..Default::default()
                },
                deps_hack::k8s_openapi::api::core::v1::ServicePort {
                    port: 2048,
                    app_protocol: Some("tcp".to_string()),
                    ..Default::default()
                },
            ]),
            selector: Some(
                vec![
                    ("key".to_string(), "value".to_string())
                ].into_iter().collect()
            ),
            publish_not_ready_addresses: Some(true),
            ..Default::default()
        };

    let service_spec = ServiceSpec::from_kube(kube_service_spec.clone());

    assert_eq!(
        service_spec.into_kube(),
        kube_service_spec
    );
}

}
