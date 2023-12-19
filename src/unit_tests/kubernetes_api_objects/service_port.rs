// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::service::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for service port
#[test]
#[verifier(external)]
pub fn test_default() {
    let service_port = ServicePort::default();
    assert_eq!(service_port.into_kube(), deps_hack::k8s_openapi::api::core::v1::ServicePort::default());
}

#[test]
#[verifier(external)]
pub fn test_set_name() {
    let mut service_port = ServicePort::default();
    service_port.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), service_port.into_kube().name.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_port() {
    let mut service_port = ServicePort::default();
    service_port.set_port(1);
    assert_eq!(1, service_port.into_kube().port);
    let mut service_port_2 = ServicePort::default();
    service_port_2.set_port(1024);
    assert_eq!(1024, service_port_2.into_kube().port);
}

#[test]
#[verifier(external)]
pub fn test_set_app_protocol() {
    let mut service_port = ServicePort::default();
    service_port.set_app_protocol(new_strlit("protocol").to_string());
    assert_eq!("protocol".to_string(), service_port.into_kube().app_protocol.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_protocaol() {
    let mut service_port = ServicePort::default();
    service_port.set_protocol(new_strlit("protocol").to_string());
    assert_eq!("protocol".to_string(), service_port.into_kube().protocol.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_service_port = deps_hack::k8s_openapi::api::core::v1::ServicePort {
        name: Some("name".to_string()),
        port: 1,
        app_protocol: Some("protocol".to_string()),
        ..Default::default()
    };

    let service_port = ServicePort::from_kube(kube_service_port.clone());

    assert_eq!(
        service_port.into_kube(),
        kube_service_port
    );
}
}
