// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::container::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::resource_requirements::*;
use crate::vstd_ext::string_map::*;
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
pub fn test_overwrite_resources(){
    let mut container = Container::default();
    let mut resources = ResourceRequirements::default();
    let mut requests = StringMap::new();
    requests.insert(new_strlit("cpu").to_string(), new_strlit("100m").to_string());
    resources.set_requests(requests);
    container. overwrite_resources(Some(resources.clone()));
    assert_eq!(resources.into_kube(), container.into_kube().resources.unwrap());
    let mut container_2 = Container::default();
    let resources_2 = None;
    container_2.overwrite_resources(resources_2);
    assert_eq!(None, container_2.into_kube().resources);
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

#[test]
#[verifier(external)]
pub fn test_set_env() {
    let env_var = EnvVar::from_kube(deps_hack::k8s_openapi::api::core::v1::EnvVar::default());
    let mut container = Container::default();
    container.set_env(vec![env_var.clone()]);
    assert_eq!(vec![env_var.into_kube()], container.into_kube().env.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_default(){
    let container = Container::default();
    assert_eq!(container.into_kube(), deps_hack::k8s_openapi::api::core::v1::Container::default());
}

#[test]
#[verifier(external)]
pub fn test_set_args(){
    let mut container = Container::default();
    container.set_args(vec![new_strlit("args").to_string()]);
    assert_eq!(vec!["args".to_string()], container.into_kube().args.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_security_context(){
    let mut container = Container::default();
    let kube_security_context =  deps_hack::k8s_openapi::api::core::v1::SecurityContext {
        run_as_user: Some(1000),
        run_as_group: Some(1000),
        privileged: Some(true),
        ..Default::default()
    };
    let security_context = SecurityContext::from_kube(kube_security_context.clone());

    container.set_security_context(security_context);
    assert_eq!(kube_security_context, container.into_kube().security_context.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_clone(){
    let mut container = Container::default();
    container.set_image(new_strlit("image").to_string());
    let container_clone = container.clone();
    assert_eq!(container.into_kube(), container_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_container = deps_hack::k8s_openapi::api::core::v1::Container {
        name: "name".to_string(),
        image: Some("image".to_string()),
        ..Default::default()
    };

    let container = Container::from_kube(kube_container.clone());

    assert_eq!(container.into_kube(),
                kube_container.clone());

    let kube_container = deps_hack::k8s_openapi::api::core::v1::Container {
        name: "name_2".to_string(),
        image: Some("image_2".to_string()),
        command: Some(vec!["command".to_string()]),
        liveness_probe: Some(deps_hack::k8s_openapi::api::core::v1::Probe {
            tcp_socket: Some(deps_hack::k8s_openapi::api::core::v1::TCPSocketAction {
                host: Some("liveness".to_string()),
                ..Default::default()
            }),
            ..Default::default()
        }),
        ..Default::default()
    };

    let container = Container::from_kube(kube_container.clone());

    assert_eq!(container.into_kube(),
                kube_container.clone());

}
}
