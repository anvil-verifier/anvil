// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::container::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for Probe
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
pub fn test_set_exec(){
    let mut probe = Probe::default();
    let mut exec_action = ExecAction::default();
    exec_action.set_command(vec![new_strlit("command").to_string()]);
    probe.set_exec(exec_action.clone());
    assert_eq!(exec_action.into_kube(), probe.into_kube().exec.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_failure_threshold() {
    let mut probe = Probe::default();
    probe.set_failure_threshold(3);
    assert_eq!(3, probe.into_kube().failure_threshold.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_initial_delay_seconds() {
    let mut probe = Probe::default();
    probe.set_initial_delay_seconds(3);
    assert_eq!(3, probe.into_kube().initial_delay_seconds.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_period_seconds() {
    let mut probe = Probe::default();
    probe.set_period_seconds(3);
    assert_eq!(3, probe.into_kube().period_seconds.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_success_threshold() {
    let mut probe = Probe::default();
    probe.set_success_threshold(3);
    assert_eq!(3, probe.into_kube().success_threshold.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_tcp_socket() {
    let mut probe = Probe::default();
    let mut tcp_socket_action = TCPSocketAction::default();
    tcp_socket_action.set_host(new_strlit("host").to_string());
    tcp_socket_action.set_port(8080);

    probe.set_tcp_socket(tcp_socket_action.clone());
    assert_eq!(tcp_socket_action.into_kube(), probe.into_kube().tcp_socket.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_timeout_seconds() {
    let mut probe = Probe::default();
    probe.set_timeout_seconds(3);
    assert_eq!(3, probe.into_kube().timeout_seconds.unwrap());
}
}
