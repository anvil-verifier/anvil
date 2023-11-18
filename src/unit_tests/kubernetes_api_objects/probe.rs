// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::container::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for Probe

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

#[test]
#[verifier(external)]
pub fn test_default() {
    let probe = Probe::default();
    assert_eq!(probe.into_kube(), deps_hack::k8s_openapi::api::core::v1::Probe::default());
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut probe = Probe::default();
    probe.set_timeout_seconds(3);
    let probe_clone = probe.clone();
    assert_eq!(probe.into_kube(), probe_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_probe = deps_hack::k8s_openapi::api::core::v1::Probe {
        failure_threshold: Some(3),
        initial_delay_seconds: Some(3),
        exec: Some(deps_hack::k8s_openapi::api::core::v1::ExecAction {
            command: Some(vec!["command".to_string()]),
        }),
        period_seconds: Some(3),
        success_threshold: Some(3),
        timeout_seconds: Some(3),
        ..Default::default()
    };

    let probe = Probe::from_kube(kube_probe.clone());

    assert_eq!(probe.into_kube(), kube_probe);
}

}
