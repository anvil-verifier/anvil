// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::{resource_requirements::*, volume::*};
use crate::kubernetes_api_objects::spec::container::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct Container {
    inner: deps_hack::k8s_openapi::api::core::v1::Container,
}

impl Container {
    pub spec fn view(&self) -> ContainerView;

    #[verifier(external_body)]
    pub fn default() -> (container: Container)
        ensures container@ == ContainerView::default(),
    {
        Container {
            inner: deps_hack::k8s_openapi::api::core::v1::Container::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures s@ == self@,
    {
        Container { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_image(&mut self, image: String)
        ensures self@ == old(self)@.set_image(image@),
    {
        self.inner.image = Some(image)
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.set_name(name@),
    {
        self.inner.name = name
    }

    #[verifier(external_body)]
    pub fn set_volume_mounts(&mut self, volume_mounts: Vec<VolumeMount>)
        ensures self@ == old(self)@.set_volume_mounts(volume_mounts@.map_values(|mount: VolumeMount| mount@)),
    {
        self.inner.volume_mounts = Some(
            volume_mounts.into_iter().map(|mount: VolumeMount| mount.into_kube()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_ports(&mut self, ports: Vec<ContainerPort>)
        ensures self@ == old(self)@.set_ports(ports@.map_values(|port: ContainerPort| port@)),
    {
        self.inner.ports = Some(ports.into_iter().map(|port: ContainerPort| port.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_lifecycle(&mut self, lifecycle: Lifecycle)
        ensures self@ == old(self)@.set_lifecycle(lifecycle@),
    {
        self.inner.lifecycle = Some(lifecycle.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_resources(&mut self, resources: ResourceRequirements)
        ensures self@ == old(self)@.set_resources(resources@),
    {
        self.inner.resources = Some(resources.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_liveness_probe(&mut self, liveness_probe: Probe)
        ensures self@ == old(self)@.set_liveness_probe(liveness_probe@),
    {
        self.inner.liveness_probe = Some(liveness_probe.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_readiness_probe(&mut self, readiness_probe: Probe)
        ensures self@ == old(self)@.set_readiness_probe(readiness_probe@),
    {
        self.inner.readiness_probe = Some(readiness_probe.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_command(&mut self, command: Vec<String>)
        ensures self@ == old(self)@.set_command(command@.map_values(|c: String| c@)),
    {
        self.inner.command = Some(command)
    }

    #[verifier(external_body)]
    pub fn set_image_pull_policy(&mut self, image_pull_policy: String)
        ensures self@ == old(self)@.set_image_pull_policy(image_pull_policy@),
    {
        self.inner.image_pull_policy = Some(image_pull_policy)
    }

    #[verifier(external_body)]
    pub fn set_env(&mut self, env: Vec<EnvVar>)
        ensures self@ == old(self)@.set_env(env@.map_values(|v: EnvVar| v@)),
    {
        self.inner.env = Some(env.into_iter().map(|e: EnvVar| e.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_args(&mut self, args: Vec<String>)
        ensures self@ == old(self)@.set_args(args@.map_values(|s: String| s@)),
    {
        self.inner.args = Some(args)
    }

    #[verifier(external_body)]
    pub fn set_security_context(&mut self, security_context: SecurityContext)
        ensures self@ == old(self)@.set_security_context(security_context@),
    {
        self.inner.security_context = Some(security_context.into_kube())
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::Container) -> Container { Container { inner: inner } }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Container { self.inner }
}

#[verifier(external_body)]
pub struct ContainerPort {
    inner: deps_hack::k8s_openapi::api::core::v1::ContainerPort,
}

impl ContainerPort {
    pub spec fn view(&self) -> ContainerPortView;

    #[verifier(external_body)]
    pub fn default() -> (container_port: ContainerPort)
        ensures container_port@ == ContainerPortView::default(),
    {
        ContainerPort { inner: deps_hack::k8s_openapi::api::core::v1::ContainerPort::default() }
    }

    pub fn new_with(name: String, port: i32) -> (container_port: ContainerPort)
        ensures container_port@ == ContainerPortView::default().set_name(name@).set_container_port(port as int),
    {
        let mut container_port = Self::default();
        container_port.set_name(name);
        container_port.set_container_port(port);

        container_port
    }

    #[verifier(external_body)]
    pub fn set_container_port(&mut self, container_port: i32)
        ensures self@ == old(self)@.set_container_port(container_port as int),
    {
        self.inner.container_port = container_port;
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.set_name(name@),
    {
        self.inner.name = Some(name);
    }

    #[verifier(external_body)]
    pub fn name(&self) -> (name: Option<String>)
        ensures opt_string_to_view(&name) == self@.name,
    {
        self.inner.name.clone()
    }

    #[verifier(external_body)]
    pub fn container_port(&self) -> (container_port: i32)
        ensures container_port == self@.container_port,
    {
        self.inner.container_port
    }

    #[verifier(external_body)]
    pub fn protocol(&self) -> (protocol: Option<String>)
        ensures opt_string_to_view(&protocol) == self@.protocol,
    {
        self.inner.protocol.clone()
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::ContainerPort) -> ContainerPort { ContainerPort { inner: inner } }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ContainerPort { self.inner }
}

#[verifier(external_body)]
pub struct VolumeMount {
    inner: deps_hack::k8s_openapi::api::core::v1::VolumeMount,
}

impl VolumeMount {
    pub spec fn view(&self) -> VolumeMountView;

    #[verifier(external_body)]
    pub fn default() -> (volume_mount: VolumeMount)
        ensures volume_mount@ == VolumeMountView::default(),
    {
        VolumeMount { inner: deps_hack::k8s_openapi::api::core::v1::VolumeMount::default() }
    }

    pub fn new_with(mount_path: String, name: String) -> (volume_mount: VolumeMount)
        ensures volume_mount@ == VolumeMountView::default().set_mount_path(mount_path@).set_name(name@),
    {
        let mut volume_mount = Self::default();
        volume_mount.set_mount_path(mount_path);
        volume_mount.set_name(name);

        volume_mount
    }

    #[verifier(external_body)]
    pub fn set_mount_path(&mut self, mount_path: String)
        ensures self@ == old(self)@.set_mount_path(mount_path@),
    {
        self.inner.mount_path = mount_path;
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.set_name(name@),
    {
        self.inner.name = name;
    }

    #[verifier(external_body)]
    pub fn set_read_only(&mut self, read_only: bool)
        ensures self@ == old(self)@.set_read_only(read_only),
    {
        self.inner.read_only = Some(read_only);
    }

    #[verifier(external_body)]
    pub fn set_sub_path(&mut self, sub_path: String)
        ensures self@ == old(self)@.set_sub_path(sub_path@),
    {
        self.inner.sub_path = Some(sub_path);
    }

    #[verifier(external_body)]
    pub fn set_mount_propagation(&mut self, mount_propagation: String)
        ensures self@ == old(self)@.set_mount_propagation(mount_propagation@),
    {
        self.inner.mount_propagation = Some(mount_propagation)
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::VolumeMount) -> VolumeMount { VolumeMount { inner: inner } }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::VolumeMount { self.inner }
}

#[verifier(external_body)]
pub struct Probe {
    inner: deps_hack::k8s_openapi::api::core::v1::Probe,
}

impl Probe {
    pub spec fn view(&self) -> ProbeView;

    #[verifier(external_body)]
    pub fn default() -> (probe: Probe)
        ensures probe@ == ProbeView::default(),
    {
        Probe { inner: deps_hack::k8s_openapi::api::core::v1::Probe::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures s@ == self@,
    {
        Probe { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_exec(&mut self, exec: ExecAction)
        ensures self@ == old(self)@.set_exec(exec@),
    {
        self.inner.exec = Some(exec.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_failure_threshold(&mut self, failure_threshold: i32)
        ensures self@ == old(self)@.set_failure_threshold(failure_threshold as int),
    {
        self.inner.failure_threshold = Some(failure_threshold);
    }

    #[verifier(external_body)]
    pub fn set_initial_delay_seconds(&mut self, initial_delay_seconds: i32)
        ensures self@ == old(self)@.set_initial_delay_seconds(initial_delay_seconds as int),
    {
        self.inner.initial_delay_seconds = Some(initial_delay_seconds);
    }

    #[verifier(external_body)]
    pub fn set_period_seconds(&mut self, period_seconds: i32)
        ensures self@ == old(self)@.set_period_seconds(period_seconds as int),
    {
        self.inner.period_seconds = Some(period_seconds);
    }

    #[verifier(external_body)]
    pub fn set_success_threshold(&mut self, success_threshold: i32)
        ensures self@ == old(self)@.set_success_threshold(success_threshold as int),
    {
        self.inner.success_threshold = Some(success_threshold);
    }

    #[verifier(external_body)]
    pub fn set_tcp_socket(&mut self, tcp_socket: TCPSocketAction)
        ensures self@ == old(self)@.set_tcp_socket(tcp_socket@),
    {
        self.inner.tcp_socket = Some(tcp_socket.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_timeout_seconds(&mut self, timeout_seconds: i32)
        ensures self@ == old(self)@.set_timeout_seconds(timeout_seconds as int),
    {
        self.inner.timeout_seconds = Some(timeout_seconds);
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::Probe) -> Probe {
        Probe { inner: inner }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Probe { self.inner }
}

#[verifier(external_body)]
pub struct ExecAction {
    inner: deps_hack::k8s_openapi::api::core::v1::ExecAction,
}

impl ExecAction {
    pub spec fn view(&self) -> ExecActionView;

    #[verifier(external_body)]
    pub fn default() -> (exec_action: ExecAction)
        ensures exec_action@ == ExecActionView::default(),
    {
        ExecAction { inner: deps_hack::k8s_openapi::api::core::v1::ExecAction::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures s@ == self@,
    {
        ExecAction { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_command(&mut self, command: Vec<String>)
        ensures self@ == old(self)@.set_command(command@.map_values(|s: String| s@)),
    {
        self.inner.command = Some(command);
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::ExecAction) -> ExecAction {
        ExecAction { inner: inner }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ExecAction { self.inner }
}

#[verifier(external_body)]
pub struct TCPSocketAction {
    inner: deps_hack::k8s_openapi::api::core::v1::TCPSocketAction,
}

impl TCPSocketAction {
    pub spec fn view(&self) -> TCPSocketActionView;

    #[verifier(external_body)]
    pub fn default() -> (tcp_socket_action: TCPSocketAction)
        ensures tcp_socket_action@ == TCPSocketActionView::default(),
    {
        TCPSocketAction { inner: deps_hack::k8s_openapi::api::core::v1::TCPSocketAction::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures s@ == self@,
    {
        TCPSocketAction { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_host(&mut self, host: String)
        ensures self@ == old(self)@.set_host(host@),
    {
        self.inner.host = Some(host);
    }

    #[verifier(external_body)]
    pub fn set_port(&mut self, port: i32)
        ensures self@ == old(self)@.set_port(port as int),
    {
        self.inner.port = deps_hack::k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(port);
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::TCPSocketAction) -> TCPSocketAction { TCPSocketAction { inner: inner } }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::TCPSocketAction {
        self.inner
    }
}

#[verifier(external_body)]
pub struct Lifecycle {
    inner: deps_hack::k8s_openapi::api::core::v1::Lifecycle,
}

impl Lifecycle {
    pub spec fn view(&self) -> LifecycleView;

    #[verifier(external_body)]
    pub fn default() -> (lifecycle: Lifecycle)
        ensures lifecycle@ == LifecycleView::default(),
    {
        Lifecycle { inner: deps_hack::k8s_openapi::api::core::v1::Lifecycle::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures s@ == self@,
    {
        Lifecycle { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_pre_stop(&mut self, handler: LifecycleHandler)
        ensures self@ == old(self)@.set_pre_stop(handler@),
    {
        self.inner.pre_stop = Some(handler.into_kube());
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::Lifecycle) -> Lifecycle { Lifecycle { inner: inner } }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Lifecycle { self.inner }
}

#[verifier(external_body)]
pub struct LifecycleHandler {
    inner: deps_hack::k8s_openapi::api::core::v1::LifecycleHandler,
}

impl LifecycleHandler {
    pub spec fn view(&self) -> LifecycleHandlerView;

    #[verifier(external_body)]
    pub fn default() -> (lifecycle_handler: LifecycleHandler)
        ensures lifecycle_handler@ == LifecycleHandlerView::default(),
    {
        LifecycleHandler { inner: deps_hack::k8s_openapi::api::core::v1::LifecycleHandler::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures s@ == self@,
    {
        LifecycleHandler { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_exec(&mut self, exec: ExecAction)
        ensures self@ == old(self)@.set_exec(exec@),
    {
        self.inner.exec = Some(exec.into_kube());
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::LifecycleHandler) -> LifecycleHandler {
        LifecycleHandler { inner: inner }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::LifecycleHandler { self.inner }
}

#[verifier(external_body)]
pub struct EnvVar {
    inner: deps_hack::k8s_openapi::api::core::v1::EnvVar,
}

impl EnvVar {
    pub spec fn view(&self) -> EnvVarView;

    #[verifier(external_body)]
    pub fn default() -> (env_var: EnvVar)
        ensures env_var@ == EnvVarView::default(),
    {
        EnvVar { inner: deps_hack::k8s_openapi::api::core::v1::EnvVar::default() }
    }

    #[verifier(external)]
    pub fn clone(&self) -> (s: Self) {
        EnvVar { inner: self.inner.clone() }
    }

    pub fn new_with(name: String, value: Option<String>, value_from: Option<EnvVarSource>) -> (env_var: EnvVar)
        ensures
            env_var@ == (EnvVarView {
                name: name@,
                value: match value {
                    Some(v) => Some(v@),
                    None => None,
                },
                value_from: match value_from {
                    Some(vf) => Some(vf@),
                    None => None,
                }
            }),
    {
        let mut env_var = EnvVar::default();
        env_var.set_name(name);
        if value.is_some() {
            env_var.set_value(value.unwrap());
        }
        if value_from.is_some() {
            env_var.set_value_from(value_from.unwrap());
        }
        env_var
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.set_name(name@),
    {
        self.inner.name = name;
    }

    #[verifier(external_body)]
    pub fn set_value(&mut self, value: String)
        ensures self@ == old(self)@.set_value(value@),
    {
        self.inner.value = Some(value)
    }

    #[verifier(external_body)]
    pub fn set_value_from(&mut self, value_from: EnvVarSource)
        ensures self@ == old(self)@.set_value_from(value_from@),
    {
        self.inner.value_from = Some(value_from.into_kube())
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::EnvVar) -> EnvVar { EnvVar { inner: inner } }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::EnvVar { self.inner }
}

#[verifier(external_body)]
pub struct EnvVarSource {
    inner: deps_hack::k8s_openapi::api::core::v1::EnvVarSource,
}

impl EnvVarSource {
    pub spec fn view(&self) -> EnvVarSourceView;

    #[verifier(external_body)]
    pub fn default() -> (env_var_source: EnvVarSource)
        ensures env_var_source@ == EnvVarSourceView::default(),
    {
        EnvVarSource { inner: deps_hack::k8s_openapi::api::core::v1::EnvVarSource::default() }
    }

    #[verifier(external)]
    pub fn clone(&self) -> (s: Self) { EnvVarSource { inner: self.inner.clone() } }

    pub fn new_with_field_ref(field_ref: ObjectFieldSelector) -> (env_var_source: EnvVarSource)
        ensures env_var_source@ == EnvVarSourceView::default().set_field_ref(field_ref@)
    {
        let mut source = EnvVarSource::default();
        source.set_field_ref(field_ref);
        source
    }

    #[verifier(external_body)]
    pub fn set_field_ref(&mut self, field_ref: ObjectFieldSelector)
        ensures self@ == old(self)@.set_field_ref(field_ref@),
    {
        self.inner.field_ref = Some(field_ref.into_kube());
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::EnvVarSource) -> EnvVarSource { EnvVarSource { inner: inner } }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::EnvVarSource { self.inner }
}

#[verifier(external_body)]
pub struct SecurityContext {
    inner: deps_hack::k8s_openapi::api::core::v1::SecurityContext,
}

impl SecurityContext {
    pub spec fn view(&self) -> SecurityContextView;

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::SecurityContext) -> SecurityContext { SecurityContext { inner: inner } }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::SecurityContext { self.inner }
}

}
