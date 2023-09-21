// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::container::*;
use crate::kubernetes_api_objects::resource::*;
use crate::kubernetes_api_objects::resource_requirements::*;
use crate::pervasive_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

#[test]
#[verifier(external)]
pub fn test_set_image() {
    let mut container = Container::default();
    container.set_image(new_strlit("image").to_string());
    assert_eq!("image".to_string(), container.into_kube().image.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_name() {
    let mut container = Container::default();
    container.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), container.into_kube().name);
}

// Tests for volume monts
#[test]
#[verifier(external)]
pub fn test_set_mount_path() {
    let mut volume_mount = VolumeMount::default();
    volume_mount.set_mount_path(new_strlit("mount_path").to_string());
    assert_eq!("mount_path".to_string(), volume_mount.into_kube().mount_path);
}

#[test]
#[verifier(external)]
pub fn test_set_name_volume_mount() {
    let mut volume_mount = VolumeMount::default();
    volume_mount.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), volume_mount.into_kube().name);
}

#[test]
#[verifier(external)]
pub fn test_set_read_only() {
    let mut volume_mount = VolumeMount::default();
    volume_mount.set_read_only(true);
    assert_eq!(true, volume_mount.into_kube().read_only.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_sub_path() {
    let mut volume_mount = VolumeMount::default();
    volume_mount.set_sub_path(new_strlit("sub_path").to_string());
    assert_eq!("sub_path".to_string(), volume_mount.into_kube().sub_path.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_volume_mounts() {
    let mut container = Container::default();
    let volume_mounts = || {
        let mut volume_mount = VolumeMount::default();
        volume_mount.set_mount_path(new_strlit("mount_path").to_string());
        volume_mount.set_read_only(true);
        volume_mount.set_sub_path(new_strlit("sub_path").to_string());
        let mut volume_mounts = Vec::new();
        volume_mounts.push(volume_mount);
        volume_mounts
    };
    container.set_volume_mounts(volume_mounts());
    assert_eq!(volume_mounts().into_iter().map(|v: VolumeMount| v.into_kube()).collect::<Vec<_>>(),
               container.into_kube().volume_mounts.unwrap());
}

// Tests for ports(ContainerPort)
#[test]
#[verifier(external)]
pub fn test_set_container_port() {
    let mut container_port = ContainerPort::default();
    container_port.set_container_port(8080);
    assert_eq!(8080, container_port.into_kube().container_port);
}

#[test]
#[verifier(external)]
pub fn test_set_name_container_port() {
    let mut container_port = ContainerPort::default();
    container_port.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), container_port.into_kube().name.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_ports() {
    let mut container = Container::default();
    let ports = || {
        let mut container_port = ContainerPort::default();
        container_port.set_container_port(8080);
        container_port.set_name(new_strlit("name").to_string());
        let mut ports = Vec::new();
        ports.push(container_port);
        ports
    };
    container.set_ports(ports());
    assert_eq!(ports().into_iter().map(|v: ContainerPort| v.into_kube()).collect::<Vec<_>>(),
               container.into_kube().ports.unwrap());
}



#[test]
#[verifier(external)]
pub fn test_set_lifecycle() {
    let mut container = Container::default();

    let mut lifecycle = Lifecycle::default();
    let mut handler = LifecycleHandler::default();
    let mut exec_action = ExecAction::default();
    exec_action.set_command(vec![new_strlit("command").to_string()]);
    handler.set_exec(exec_action);
    lifecycle.set_pre_stop(handler);

    container.set_lifecycle(lifecycle.clone());
    assert_eq!(lifecycle.into_kube(), container.into_kube().lifecycle.unwrap());
}

// Tests for resources
#[test]
#[verifier(external)]
pub fn test_set_resources() {
    let mut container = Container::default();

    let mut resources = ResourceRequirements::default();
    let mut requests = StringMap::new();
    requests.insert(new_strlit("cpu").to_string(), new_strlit("100m").to_string());
    resources.set_requests(requests);

    container.set_resources(resources.clone());
    assert_eq!(resources.into_kube(), container.into_kube().resources.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_liveness_probe() {
    let mut container = Container::default();
    let mut probe = Probe::default();
    let mut tcp_socket_action = TCPSocketAction::default();
    tcp_socket_action.set_host(new_strlit("liveness").to_string());
    tcp_socket_action.set_port(2196);
    probe.set_tcp_socket(tcp_socket_action);

    container.set_liveness_probe(probe.clone());
    assert_eq!(probe.into_kube(), container.into_kube().liveness_probe.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_readiness_probe() {
    let mut container = Container::default();
    let mut probe = Probe::default();
    let mut tcp_socket_action = TCPSocketAction::default();
    tcp_socket_action.set_host(new_strlit("readiness").to_string());
    tcp_socket_action.set_port(2196);
    probe.set_tcp_socket(tcp_socket_action);

    container.set_readiness_probe(probe.clone());
    assert_eq!(probe.into_kube(), container.into_kube().readiness_probe.unwrap());
}

// Tests for command and image pull policy
#[test]
#[verifier(external)]
pub fn test_set_command() {
    let mut container = Container::default();
    container.set_command(vec![new_strlit("command").to_string()]);
    assert_eq!(vec!["command".to_string()], container.into_kube().command.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_image_pull_policy() {
    let mut container = Container::default();
    container.set_image_pull_policy(new_strlit("image_pull_policy").to_string());
    assert_eq!("image_pull_policy".to_string(), container.into_kube().image_pull_policy.unwrap());
}

// Test for Envs
#[test]
#[verifier(external)]
pub fn test_set_env() {
    let env_var = EnvVar::from_kube(deps_hack::k8s_openapi::api::core::v1::EnvVar::default());
    let mut container = Container::default();
    container.set_env(vec![env_var.clone()]);
    assert_eq!(vec![env_var.into_kube()], container.into_kube().env.unwrap());
}
}
