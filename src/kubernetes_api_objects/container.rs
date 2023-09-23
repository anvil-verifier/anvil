// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, marshal::*, resource::*, resource_requirements::*,
    volume::*,
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

#[verifier(external_body)]
pub struct Container {
    inner: deps_hack::k8s_openapi::api::core::v1::Container,
}

impl Container {
    pub spec fn view(&self) -> ContainerView;

    #[verifier(external_body)]
    pub fn default() -> (container: Container)
        ensures
            container@ == ContainerView::default(),
    {
        Container {
            inner: deps_hack::k8s_openapi::api::core::v1::Container::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures
            s@ == self@,
    {
        Container { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_image(&mut self, image: String)
        ensures
            self@ == old(self)@.set_image(image@),
    {
        self.inner.image = Some(image.into_rust_string())
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = name.into_rust_string()
    }

    #[verifier(external_body)]
    pub fn set_volume_mounts(&mut self, volume_mounts: Vec<VolumeMount>)
        ensures
            self@ == old(self)@.set_volume_mounts(volume_mounts@.map_values(|mount: VolumeMount| mount@)),
    {
        self.inner.volume_mounts = Some(
            volume_mounts.into_iter().map(|mount: VolumeMount| mount.into_kube()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_ports(&mut self, ports: Vec<ContainerPort>)
        ensures
            self@ == old(self)@.set_ports(ports@.map_values(|port: ContainerPort| port@)),
    {
        self.inner.ports = Some(
            ports.into_iter().map(|port: ContainerPort| port.into_kube()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_lifecycle(&mut self, lifecycle: Lifecycle)
        ensures
            self@ == old(self)@.set_lifecycle(lifecycle@),
    {
        self.inner.lifecycle = Some(lifecycle.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_resources(&mut self, resources: ResourceRequirements)
        ensures
            self@ == old(self)@.set_resources(resources@),
    {
        self.inner.resources = Some(resources.into_kube())
    }

    #[verifier(external_body)]
    pub fn overwrite_resources(&mut self, resources: Option<ResourceRequirements>)
        ensures
            resources.is_None() ==> self@ == old(self)@.unset_resources(),
            resources.is_Some() ==> self@ == old(self)@.set_resources(resources.get_Some_0()@),
    {
        match resources {
            Some(r) => {
                self.inner.resources = Some(r.into_kube())
            },
            None => {
                self.inner.resources = None
            }
        }
    }

    #[verifier(external_body)]
    pub fn set_liveness_probe(&mut self, liveness_probe: Probe)
        ensures
            self@ == old(self)@.set_liveness_probe(liveness_probe@),
    {
        self.inner.liveness_probe = Some(liveness_probe.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_readiness_probe(&mut self, readiness_probe: Probe)
        ensures
            self@ == old(self)@.set_readiness_probe(readiness_probe@),
    {
        self.inner.readiness_probe = Some(readiness_probe.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_command(&mut self, command: Vec<String>)
        ensures
            self@ == old(self)@.set_command(command@.map_values(|c: String| c@)),
    {
        self.inner.command = Some(
            command.into_iter().map(|c: String| c.into_rust_string()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_image_pull_policy(&mut self, image_pull_policy: String)
        ensures
            self@ == old(self)@.set_image_pull_policy(image_pull_policy@),
    {
        self.inner.image_pull_policy = Some(image_pull_policy.into_rust_string())
    }

    #[verifier(external_body)]
    pub fn set_env(&mut self, env: Vec<EnvVar>)
        ensures
            self@ == old(self)@.set_env(env@.map_values(|v: EnvVar| v@)),
    {
        self.inner.env = Some(
            env.into_iter().map(|e: EnvVar| e.into_kube()).collect()
        )
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Container {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ContainerPort {
    inner: deps_hack::k8s_openapi::api::core::v1::ContainerPort,
}

impl ContainerPort {
    pub spec fn view(&self) -> ContainerPortView;

    #[verifier(external_body)]
    pub fn default() -> (container_port: ContainerPort)
        ensures
            container_port@ == ContainerPortView::default(),
    {
        ContainerPort {
            inner: deps_hack::k8s_openapi::api::core::v1::ContainerPort::default(),
        }
    }

    pub fn new_with(name: String, port: i32) -> (container_port: ContainerPort)
        ensures
            container_port@ == ContainerPortView::default().set_name(name@).set_container_port(port as int),
    {
        let mut container_port = Self::default();
        container_port.set_name(name);
        container_port.set_container_port(port);

        container_port
    }

    #[verifier(external_body)]
    pub fn set_container_port(&mut self, container_port: i32)
        ensures
            self@ == old(self)@.set_container_port(container_port as int),
    {
        self.inner.container_port = container_port;
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = Some(name.into_rust_string());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ContainerPort {
        self.inner
    }
}

#[verifier(external_body)]
pub struct VolumeMount {
    inner: deps_hack::k8s_openapi::api::core::v1::VolumeMount,
}

impl VolumeMount {
    pub spec fn view(&self) -> VolumeMountView;

    #[verifier(external_body)]
    pub fn default() -> (volume_mount: VolumeMount)
        ensures
            volume_mount@ == VolumeMountView::default(),
    {
        VolumeMount {
            inner: deps_hack::k8s_openapi::api::core::v1::VolumeMount::default(),
        }
    }

    pub fn new_with(mount_path: String, name: String) -> (volume_mount: VolumeMount)
        ensures
            volume_mount@ == VolumeMountView::default().set_mount_path(mount_path@).set_name(name@),
    {
        let mut volume_mount = Self::default();
        volume_mount.set_mount_path(mount_path);
        volume_mount.set_name(name);

        volume_mount
    }

    #[verifier(external_body)]
    pub fn set_mount_path(&mut self, mount_path: String)
        ensures
            self@ == old(self)@.set_mount_path(mount_path@),
    {
        self.inner.mount_path = mount_path.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = name.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_read_only(&mut self, read_only: bool)
        ensures
            self@ == old(self)@.set_read_only(read_only),
    {
        self.inner.read_only = Some(read_only);
    }

    #[verifier(external_body)]
    pub fn set_sub_path(&mut self, sub_path: String)
        ensures
            self@ == old(self)@.set_sub_path(sub_path@),
    {
        self.inner.sub_path = Some(sub_path.into_rust_string());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::VolumeMount {
        self.inner
    }
}

#[verifier(external_body)]
pub struct Probe {
    inner: deps_hack::k8s_openapi::api::core::v1::Probe,
}

impl Probe {
    pub spec fn view(&self) -> ProbeView;

    #[verifier(external_body)]
    pub fn default() -> (probe: Probe)
        ensures
            probe@ == ProbeView::default(),
    {
        Probe {
            inner: deps_hack::k8s_openapi::api::core::v1::Probe::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures
            s@ == self@,
    {
        Probe { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_exec(&mut self, exec: ExecAction)
        ensures
            self@ == old(self)@.set_exec(exec@),
    {
        self.inner.exec = Some(exec.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_failure_threshold(&mut self, failure_threshold: i32)
        ensures
            self@ == old(self)@.set_failure_threshold(failure_threshold as int),
    {
        self.inner.failure_threshold = Some(failure_threshold);
    }

    #[verifier(external_body)]
    pub fn set_initial_delay_seconds(&mut self, initial_delay_seconds: i32)
        ensures
            self@ == old(self)@.set_initial_delay_seconds(initial_delay_seconds as int),
    {
        self.inner.initial_delay_seconds = Some(initial_delay_seconds);
    }

    #[verifier(external_body)]
    pub fn set_period_seconds(&mut self, period_seconds: i32)
        ensures
            self@ == old(self)@.set_period_seconds(period_seconds as int),
    {
        self.inner.period_seconds = Some(period_seconds);
    }

    #[verifier(external_body)]
    pub fn set_success_threshold(&mut self, success_threshold: i32)
        ensures
            self@ == old(self)@.set_success_threshold(success_threshold as int),
    {
        self.inner.success_threshold = Some(success_threshold);
    }

    #[verifier(external_body)]
    pub fn set_tcp_socket(&mut self, tcp_socket: TCPSocketAction)
        ensures
            self@ == old(self)@.set_tcp_socket(tcp_socket@),
    {
        self.inner.tcp_socket = Some(tcp_socket.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_timeout_seconds(&mut self, timeout_seconds: i32)
        ensures
            self@ == old(self)@.set_timeout_seconds(timeout_seconds as int),
    {
        self.inner.timeout_seconds = Some(timeout_seconds);
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::Probe) -> Probe {
        Probe { inner: inner }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Probe {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ExecAction {
    inner: deps_hack::k8s_openapi::api::core::v1::ExecAction,
}

impl ExecAction {
    pub spec fn view(&self) -> ExecActionView;

    #[verifier(external_body)]
    pub fn default() -> (exec_action: ExecAction)
        ensures
            exec_action@ == ExecActionView::default(),
    {
        ExecAction {
            inner: deps_hack::k8s_openapi::api::core::v1::ExecAction::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures
            s@ == self@,
    {
        ExecAction { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_command(&mut self, command: Vec<String>)
        ensures
            self@ == old(self)@.set_command(command@.map_values(|s: String| s@)),
    {
        self.inner.command = Some(command.into_iter().map(|s: String| s.into_rust_string()).collect());
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::ExecAction) -> ExecAction {
        ExecAction { inner: inner }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ExecAction {
        self.inner
    }
}

#[verifier(external_body)]
pub struct TCPSocketAction {
    inner: deps_hack::k8s_openapi::api::core::v1::TCPSocketAction,
}

impl TCPSocketAction {
    pub spec fn view(&self) -> TCPSocketActionView;

    #[verifier(external_body)]
    pub fn default() -> (tcp_socket_action: TCPSocketAction)
        ensures
            tcp_socket_action@ == TCPSocketActionView::default(),
    {
        TCPSocketAction {
            inner: deps_hack::k8s_openapi::api::core::v1::TCPSocketAction::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures
            s@ == self@,
    {
        TCPSocketAction { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_host(&mut self, host: String)
        ensures
            self@ == old(self)@.set_host(host@),
    {
        self.inner.host = Some(host.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_port(&mut self, port: i32)
        ensures
            self@ == old(self)@.set_port(port as int),
    {
        self.inner.port = deps_hack::k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(port);
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::TCPSocketAction) -> TCPSocketAction {
        TCPSocketAction { inner: inner }
    }

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
        ensures
            lifecycle@ == LifecycleView::default(),
    {
        Lifecycle {
            inner: deps_hack::k8s_openapi::api::core::v1::Lifecycle::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures
            s@ == self@,
    {
        Lifecycle { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_pre_stop(&mut self, handler: LifecycleHandler)
        ensures
            self@ == old(self)@.set_pre_stop(handler@),
    {
        self.inner.pre_stop = Some(handler.into_kube());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Lifecycle {
        self.inner
    }
}

#[verifier(external_body)]
pub struct LifecycleHandler {
    inner: deps_hack::k8s_openapi::api::core::v1::LifecycleHandler,
}

impl LifecycleHandler {
    pub spec fn view(&self) -> LifecycleHandlerView;

    #[verifier(external_body)]
    pub fn default() -> (lifecycle_handler: LifecycleHandler)
        ensures
            lifecycle_handler@ == LifecycleHandlerView::default(),
    {
        LifecycleHandler {
            inner: deps_hack::k8s_openapi::api::core::v1::LifecycleHandler::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures
            s@ == self@,
    {
        LifecycleHandler { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_exec(&mut self, exec: ExecAction)
        ensures
            self@ == old(self)@.set_exec(exec@),
    {
        self.inner.exec = Some(exec.into_kube());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::LifecycleHandler {
        self.inner
    }
}

#[verifier(external_body)]
pub struct EnvVar {
    inner: deps_hack::k8s_openapi::api::core::v1::EnvVar,
}

impl EnvVar {
    pub spec fn view(&self) -> EnvVarView;

    #[verifier(external_body)]
    pub fn default() -> (env_var: EnvVar)
        ensures
            env_var@ == EnvVarView::default(),
    {
        EnvVar {
            inner: deps_hack::k8s_openapi::api::core::v1::EnvVar::default(),
        }
    }

    #[verifier(external)]
    pub fn clone(&self) -> (s: Self) {
        EnvVar { inner: self.inner.clone() }
    }

    pub fn new_with(name: String, value: Option<String>, value_from: Option<EnvVarSource>) -> (env_var: EnvVar)
        ensures
            env_var@ == EnvVarView::default().set_name(name@).overwrite_value({
                if value.is_Some() { Some(value.get_Some_0()@) } else { None }
            }).overwrite_value_from({
                if value_from.is_Some() { Some(value_from.get_Some_0()@) } else { None }
            }),
    {
        let mut env_var = EnvVar::default();
        env_var.set_name(name);
        env_var.overwrite_value(value);
        env_var.overwrite_value_from(value_from);
        env_var
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = name.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn overwrite_value(&mut self, value: Option<String>)
        ensures
            value.is_Some() ==> self@ == old(self)@.overwrite_value(Some(value.get_Some_0()@)),
            value.is_None() ==> self@ == old(self)@.overwrite_value(None),
    {
        match value {
            Some(v) => self.inner.value = Some(v.into_rust_string()),
            None => self.inner.value = None,
        }
    }

    #[verifier(external_body)]
    pub fn overwrite_value_from(&mut self, value_from: Option<EnvVarSource>)
        ensures
            value_from.is_Some() ==> self@ == old(self)@.overwrite_value_from(Some(value_from.get_Some_0()@)),
            value_from.is_None() ==> self@ == old(self)@.overwrite_value_from(None),
    {
        match value_from {
            Some(v) => self.inner.value_from = Some(v.into_kube()),
            None => self.inner.value_from = None,
        }

    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::EnvVar) -> EnvVar {
        EnvVar { inner: inner }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::EnvVar {
        self.inner
    }
}

#[verifier(external_body)]
pub struct EnvVarSource {
    inner: deps_hack::k8s_openapi::api::core::v1::EnvVarSource,
}

impl EnvVarSource {
    pub spec fn view(&self) -> EnvVarSourceView;

    #[verifier(external_body)]
    pub fn default() -> (env_var_source: EnvVarSource)
        ensures
            env_var_source@ == EnvVarSourceView::default(),
    {
        EnvVarSource {
            inner: deps_hack::k8s_openapi::api::core::v1::EnvVarSource::default(),
        }
    }

    #[verifier(external)]
    pub fn clone(&self) -> (s: Self) {
        EnvVarSource { inner: self.inner.clone() }
    }

    pub fn new_with_field_ref(field_ref: ObjectFieldSelector) -> (env_var_source: EnvVarSource)
        ensures
            env_var_source@ == EnvVarSourceView::default().set_field_ref(field_ref@)
    {
        let mut source = EnvVarSource::default();
        source.set_field_ref(field_ref);
        source
    }

    #[verifier(external_body)]
    pub fn set_field_ref(&mut self, field_ref: ObjectFieldSelector)
        ensures
            self@ == old(self)@.set_field_ref(field_ref@),
    {
        self.inner.field_ref = Some(field_ref.into_kube());
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::EnvVarSource) -> EnvVarSource {
        EnvVarSource { inner: inner }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::EnvVarSource {
        self.inner
    }
}

pub struct ContainerView {
    pub env: Option<Seq<EnvVarView>>,
    pub image: Option<StringView>,
    pub name: StringView,
    pub ports: Option<Seq<ContainerPortView>>,
    pub volume_mounts: Option<Seq<VolumeMountView>>,
    pub lifecycle: Option<LifecycleView>,
    pub resources: Option<ResourceRequirementsView>,
    pub readiness_probe: Option<ProbeView>,
    pub liveness_probe: Option<ProbeView>,
    pub command: Option<Seq<StringView>>,
    pub image_pull_policy: Option<StringView>,
}

impl ContainerView {
    pub open spec fn default() -> ContainerView {
        ContainerView {
            env: None,
            image: None,
            name: new_strlit("")@,
            ports: None,
            volume_mounts: None,
            lifecycle: None,
            resources: None,
            readiness_probe: None,
            liveness_probe: None,
            command: None,
            image_pull_policy: None,
        }
    }

    pub open spec fn set_env(self, env: Seq<EnvVarView>) -> ContainerView {
        ContainerView {
            env: Some(env),
            ..self
        }
    }

    pub open spec fn set_image(self, image: StringView) -> ContainerView {
        ContainerView {
            image: Some(image),
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ContainerView {
        ContainerView {
            name: name,
            ..self
        }
    }

    pub open spec fn set_ports(self, ports: Seq<ContainerPortView>) -> ContainerView {
        ContainerView {
            ports: Some(ports),
            ..self
        }
    }

    pub open spec fn set_volume_mounts(self, volume_mounts: Seq<VolumeMountView>) -> ContainerView {
        ContainerView {
            volume_mounts: Some(volume_mounts),
            ..self
        }
    }

    pub open spec fn set_lifecycle(self, lifecycle: LifecycleView) -> ContainerView {
        ContainerView {
            lifecycle: Some(lifecycle),
            ..self
        }
    }

    pub open spec fn set_resources(self, resources: ResourceRequirementsView) -> ContainerView {
        ContainerView {
            resources: Some(resources),
            ..self
        }
    }

    pub open spec fn unset_resources(self) -> ContainerView {
        ContainerView {
            resources: None,
            ..self
        }
    }

    pub open spec fn set_readiness_probe(self, readiness_probe: ProbeView) -> ContainerView {
        ContainerView {
            readiness_probe: Some(readiness_probe),
            ..self
        }
    }

    pub open spec fn set_liveness_probe(self, liveness_probe: ProbeView) -> ContainerView {
        ContainerView {
            liveness_probe: Some(liveness_probe),
            ..self
        }
    }

    pub open spec fn set_command(self, command: Seq<StringView>) -> ContainerView {
        ContainerView {
            command: Some(command),
            ..self
        }
    }

    pub open spec fn set_image_pull_policy(self, image_pull_policy: StringView) -> ContainerView {
        ContainerView {
            image_pull_policy: Some(image_pull_policy),
            ..self
        }
    }
}

pub struct LifecycleView {
    pub pre_stop: Option<LifecycleHandlerView>,
}

impl LifecycleView {
    pub open spec fn default() -> LifecycleView {
        LifecycleView {
            pre_stop: None,
        }
    }

    pub open spec fn set_pre_stop(self, pre_stop: LifecycleHandlerView) -> LifecycleView {
        LifecycleView {
            pre_stop: Some(pre_stop),
            ..self
        }
    }
}

pub struct LifecycleHandlerView {
    pub exec_: Option<ExecActionView>,
}

impl LifecycleHandlerView {
    pub open spec fn default() -> LifecycleHandlerView {
        LifecycleHandlerView {
            exec_: None,
        }
    }

    pub open spec fn set_exec(self, exec: ExecActionView) -> LifecycleHandlerView {
        LifecycleHandlerView {
            exec_: Some(exec),
            ..self
        }
    }
}

pub struct ContainerPortView {
    pub container_port: int,
    pub name: Option<StringView>,
}

impl ContainerPortView {
    pub open spec fn default() -> ContainerPortView {
        ContainerPortView {
            container_port: 0, // TODO: is this the correct default value?
            name: None,
        }
    }

    pub open spec fn set_container_port(self, container_port: int) -> ContainerPortView {
        ContainerPortView {
            container_port: container_port,
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ContainerPortView {
        ContainerPortView {
            name: Some(name),
            ..self
        }
    }
}

pub struct VolumeMountView {
    pub mount_path: StringView,
    pub name: StringView,
    pub read_only: Option<bool>,
    pub sub_path: Option<StringView>,
}

impl VolumeMountView {
    pub open spec fn default() -> VolumeMountView {
        VolumeMountView {
            mount_path: new_strlit("")@,
            name: new_strlit("")@,
            read_only: Some(false),
            sub_path: None,
        }
    }

    pub open spec fn set_mount_path(self, mount_path: StringView) -> VolumeMountView {
        VolumeMountView {
            mount_path: mount_path,
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> VolumeMountView {
        VolumeMountView {
            name: name,
            ..self
        }
    }

    pub open spec fn set_read_only(self, read_only: bool) -> VolumeMountView {
        VolumeMountView {
            read_only: Some(read_only),
            ..self
        }
    }

    pub open spec fn set_sub_path(self, sub_path: StringView) -> VolumeMountView {
        VolumeMountView {
            sub_path: Some(sub_path),
            ..self
        }
    }
}

pub struct ProbeView {
    pub exec_: Option<ExecActionView>,
    pub failure_threshold: Option<int>,
    pub initial_delay_seconds: Option<int>,
    pub period_seconds: Option<int>,
    pub success_threshold: Option<int>,
    pub tcp_socket: Option<TCPSocketActionView>,
    pub timeout_seconds: Option<int>,
}

impl ProbeView {
    pub open spec fn default() -> ProbeView {
        ProbeView {
            exec_: None,
            failure_threshold: None,
            initial_delay_seconds: None,
            period_seconds: None,
            success_threshold: None,
            tcp_socket: None,
            timeout_seconds: None,
        }
    }

    pub open spec fn set_exec(self, exec: ExecActionView) -> ProbeView {
        ProbeView {
            exec_: Some(exec),
            ..self
        }
    }

    pub open spec fn set_failure_threshold(self, failure_threshold: int) -> ProbeView {
        ProbeView {
            failure_threshold: Some(failure_threshold),
            ..self
        }
    }

    pub open spec fn set_initial_delay_seconds(self, initial_delay_seconds: int) -> ProbeView {
        ProbeView {
            initial_delay_seconds: Some(initial_delay_seconds),
            ..self
        }
    }

    pub open spec fn set_period_seconds(self, period_seconds: int) -> ProbeView {
        ProbeView {
            period_seconds: Some(period_seconds),
            ..self
        }
    }

    pub open spec fn set_success_threshold(self, success_threshold: int) -> ProbeView {
        ProbeView {
            success_threshold: Some(success_threshold),
            ..self
        }
    }

    pub open spec fn set_tcp_socket(self, tcp_socket: TCPSocketActionView) -> ProbeView {
        ProbeView {
            tcp_socket: Some(tcp_socket),
            ..self
        }
    }

    pub open spec fn set_timeout_seconds(self, timeout_seconds: int) -> ProbeView {
        ProbeView {
            timeout_seconds: Some(timeout_seconds),
            ..self
        }
    }
}

pub struct ExecActionView {
    pub command: Option<Seq<StringView>>,
}

impl ExecActionView {
    pub open spec fn default() -> ExecActionView {
        ExecActionView {
            command: None,
        }
    }

    pub open spec fn set_command(self, command: Seq<StringView>) -> ExecActionView {
        ExecActionView {
            command: Some(command),
            ..self
        }
    }
}

pub struct TCPSocketActionView {
    pub host: Option<StringView>,
    pub port: int,
}

impl TCPSocketActionView {
    pub open spec fn default() -> TCPSocketActionView {
        TCPSocketActionView {
            host: None,
            port: 0,
        }
    }

    pub open spec fn set_host(self, host: StringView) -> TCPSocketActionView {
        TCPSocketActionView {
            host: Some(host),
            ..self
        }
    }

    pub open spec fn set_port(self, port: int) -> TCPSocketActionView {
        TCPSocketActionView {
            port: port,
            ..self
        }
    }
}

pub struct EnvVarView {
    pub name: StringView,
    pub value: Option<StringView>,
    pub value_from: Option<EnvVarSourceView>,
}

impl EnvVarView {
    pub open spec fn default() -> EnvVarView {
        EnvVarView {
            name: new_strlit("")@,
            value: None,
            value_from: None,
        }
    }

    pub open spec fn set_name(self, name: StringView) -> EnvVarView {
        EnvVarView {
            name: name,
            ..self
        }
    }

    pub open spec fn overwrite_value(self, value: Option<StringView>) -> EnvVarView {
        EnvVarView {
            value: value,
            ..self
        }
    }

    pub open spec fn overwrite_value_from(self, value_from: Option<EnvVarSourceView>) -> EnvVarView {
        EnvVarView {
            value_from: value_from,
            ..self
        }
    }
}

pub struct EnvVarSourceView {
    pub field_ref: Option<ObjectFieldSelectorView>,
}

impl EnvVarSourceView {
    pub open spec fn default() -> EnvVarSourceView {
        EnvVarSourceView {
            field_ref: None,
        }
    }

    pub open spec fn set_field_ref(self, field_ref: ObjectFieldSelectorView) -> EnvVarSourceView {
        EnvVarSourceView {
            field_ref: Some(field_ref),
            ..self
        }
    }
}

}
