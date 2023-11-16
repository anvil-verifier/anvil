// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::container::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for life cycle
#[test]
#[verifier(external)]
pub fn test_set_host() {
    let mut tcp_socket_action = TCPSocketAction::default();
    tcp_socket_action.set_host(new_strlit("host").to_string());
    assert_eq!("host".to_string(), tcp_socket_action.into_kube().host.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_port() {
    let mut tcp_socket_action = TCPSocketAction::default();
    tcp_socket_action.set_port(8080);
    assert_eq!(deps_hack::k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(8080),
               tcp_socket_action.into_kube().port);
}

#[test]
#[verifier(external)]
pub fn test_default() {
    let tcp_socket_action = TCPSocketAction::default();
    assert_eq!(tcp_socket_action.into_kube(), deps_hack::k8s_openapi::api::core::v1::TCPSocketAction::default());
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut tcp_socket_action = TCPSocketAction::default();
    tcp_socket_action.set_host(new_strlit("host").to_string());
    tcp_socket_action.set_port(8080);
    let tcp_socket_action_clone = tcp_socket_action.clone();
    assert_eq!(tcp_socket_action.into_kube(), tcp_socket_action_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_tcp_socket_action = deps_hack::k8s_openapi::api::core::v1::TCPSocketAction {
        host: Some("host".to_string()),
        port: deps_hack::k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(8080),
    };

    let tcp_socket_action = TCPSocketAction::from_kube(kube_tcp_socket_action.clone());

    assert_eq!(tcp_socket_action.into_kube(),
                kube_tcp_socket_action);

}
}
