// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::{resource::*, resource_requirements::*, volume::*};
use crate::kubernetes_api_objects::spec::container::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

implement_field_wrapper_type!(
    Container,
    k8s_openapi::api::core::v1::Container,
    ContainerView
);

implement_field_wrapper_type!(
    ContainerPort,
    k8s_openapi::api::core::v1::ContainerPort,
    ContainerPortView
);

implement_field_wrapper_type!(
    VolumeMount,
    k8s_openapi::api::core::v1::VolumeMount,
    VolumeMountView
);

implement_field_wrapper_type!(
    Probe,
    k8s_openapi::api::core::v1::Probe,
    ProbeView
);

implement_field_wrapper_type!(
    ExecAction,
    k8s_openapi::api::core::v1::ExecAction,
    ExecActionView
);

implement_field_wrapper_type!(
    TCPSocketAction,
    k8s_openapi::api::core::v1::TCPSocketAction,
    TCPSocketActionView
);

implement_field_wrapper_type!(
    Lifecycle,
    k8s_openapi::api::core::v1::Lifecycle,
    LifecycleView
);

implement_field_wrapper_type!(
    LifecycleHandler,
    k8s_openapi::api::core::v1::LifecycleHandler,
    LifecycleHandlerView
);

implement_field_wrapper_type!(
    EnvVar,
    k8s_openapi::api::core::v1::EnvVar,
    EnvVarView
);

implement_field_wrapper_type!(
    EnvVarSource,
    k8s_openapi::api::core::v1::EnvVarSource,
    EnvVarSourceView
);

implement_field_wrapper_type!(
    SecurityContext,
    k8s_openapi::api::core::v1::SecurityContext,
    SecurityContextView
);

impl Container {
    #[verifier(external_body)]
    pub fn set_image(&mut self, image: String)
        ensures self@ == old(self)@.with_image(image@),
    {
        self.inner.image = Some(image)
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.with_name(name@),
    {
        self.inner.name = name
    }

    #[verifier(external_body)]
    pub fn set_volume_mounts(&mut self, volume_mounts: Vec<VolumeMount>)
        ensures self@ == old(self)@.with_volume_mounts(volume_mounts.deep_view()),
    {
        self.inner.volume_mounts = Some(
            volume_mounts.into_iter().map(|mount: VolumeMount| mount.into_kube()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_ports(&mut self, ports: Vec<ContainerPort>)
        ensures self@ == old(self)@.with_ports(ports.deep_view()),
    {
        self.inner.ports = Some(ports.into_iter().map(|port: ContainerPort| port.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_lifecycle(&mut self, lifecycle: Lifecycle)
        ensures self@ == old(self)@.with_lifecycle(lifecycle@),
    {
        self.inner.lifecycle = Some(lifecycle.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_resources(&mut self, resources: ResourceRequirements)
        ensures self@ == old(self)@.with_resources(resources@),
    {
        self.inner.resources = Some(resources.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_liveness_probe(&mut self, liveness_probe: Probe)
        ensures self@ == old(self)@.with_liveness_probe(liveness_probe@),
    {
        self.inner.liveness_probe = Some(liveness_probe.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_readiness_probe(&mut self, readiness_probe: Probe)
        ensures self@ == old(self)@.with_readiness_probe(readiness_probe@),
    {
        self.inner.readiness_probe = Some(readiness_probe.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_command(&mut self, command: Vec<String>)
        ensures self@ == old(self)@.with_command(command.deep_view()),
    {
        self.inner.command = Some(command)
    }

    #[verifier(external_body)]
    pub fn set_image_pull_policy(&mut self, image_pull_policy: String)
        ensures self@ == old(self)@.with_image_pull_policy(image_pull_policy@),
    {
        self.inner.image_pull_policy = Some(image_pull_policy)
    }

    #[verifier(external_body)]
    pub fn set_env(&mut self, env: Vec<EnvVar>)
        ensures self@ == old(self)@.with_env(env.deep_view()),
    {
        self.inner.env = Some(env.into_iter().map(|e: EnvVar| e.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_args(&mut self, args: Vec<String>)
        ensures self@ == old(self)@.with_args(args.deep_view()),
    {
        self.inner.args = Some(args)
    }

    #[verifier(external_body)]
    pub fn set_security_context(&mut self, security_context: SecurityContext)
        ensures self@ == old(self)@.with_security_context(security_context@),
    {
        self.inner.security_context = Some(security_context.into_kube())
    }
}

impl ContainerPort {
    pub fn new_with(name: String, port: i32) -> (container_port: ContainerPort)
        ensures container_port@ == ContainerPortView::default().with_name(name@).with_container_port(port as int),
    {
        let mut container_port = Self::default();
        container_port.set_name(name);
        container_port.set_container_port(port);

        container_port
    }

    #[verifier(external_body)]
    pub fn set_container_port(&mut self, container_port: i32)
        ensures self@ == old(self)@.with_container_port(container_port as int),
    {
        self.inner.container_port = container_port;
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.with_name(name@),
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
}

impl VolumeMount {
    pub fn new_with(mount_path: String, name: String) -> (volume_mount: VolumeMount)
        ensures volume_mount@ == VolumeMountView::default().with_mount_path(mount_path@).with_name(name@),
    {
        let mut volume_mount = Self::default();
        volume_mount.set_mount_path(mount_path);
        volume_mount.set_name(name);

        volume_mount
    }

    #[verifier(external_body)]
    pub fn set_mount_path(&mut self, mount_path: String)
        ensures self@ == old(self)@.with_mount_path(mount_path@),
    {
        self.inner.mount_path = mount_path;
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.with_name(name@),
    {
        self.inner.name = name;
    }

    #[verifier(external_body)]
    pub fn set_read_only(&mut self, read_only: bool)
        ensures self@ == old(self)@.with_read_only(read_only),
    {
        self.inner.read_only = Some(read_only);
    }

    #[verifier(external_body)]
    pub fn set_sub_path(&mut self, sub_path: String)
        ensures self@ == old(self)@.with_sub_path(sub_path@),
    {
        self.inner.sub_path = Some(sub_path);
    }

    #[verifier(external_body)]
    pub fn set_mount_propagation(&mut self, mount_propagation: String)
        ensures self@ == old(self)@.with_mount_propagation(mount_propagation@),
    {
        self.inner.mount_propagation = Some(mount_propagation)
    }
}

impl Probe {
    #[verifier(external_body)]
    pub fn set_exec(&mut self, exec: ExecAction)
        ensures self@ == old(self)@.with_exec(exec@),
    {
        self.inner.exec = Some(exec.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_failure_threshold(&mut self, failure_threshold: i32)
        ensures self@ == old(self)@.with_failure_threshold(failure_threshold as int),
    {
        self.inner.failure_threshold = Some(failure_threshold);
    }

    #[verifier(external_body)]
    pub fn set_initial_delay_seconds(&mut self, initial_delay_seconds: i32)
        ensures self@ == old(self)@.with_initial_delay_seconds(initial_delay_seconds as int),
    {
        self.inner.initial_delay_seconds = Some(initial_delay_seconds);
    }

    #[verifier(external_body)]
    pub fn set_period_seconds(&mut self, period_seconds: i32)
        ensures self@ == old(self)@.with_period_seconds(period_seconds as int),
    {
        self.inner.period_seconds = Some(period_seconds);
    }

    #[verifier(external_body)]
    pub fn set_success_threshold(&mut self, success_threshold: i32)
        ensures self@ == old(self)@.with_success_threshold(success_threshold as int),
    {
        self.inner.success_threshold = Some(success_threshold);
    }

    #[verifier(external_body)]
    pub fn set_tcp_socket(&mut self, tcp_socket: TCPSocketAction)
        ensures self@ == old(self)@.with_tcp_socket(tcp_socket@),
    {
        self.inner.tcp_socket = Some(tcp_socket.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_timeout_seconds(&mut self, timeout_seconds: i32)
        ensures self@ == old(self)@.with_timeout_seconds(timeout_seconds as int),
    {
        self.inner.timeout_seconds = Some(timeout_seconds);
    }
}

impl ExecAction {
    #[verifier(external_body)]
    pub fn set_command(&mut self, command: Vec<String>)
        ensures self@ == old(self)@.with_command(command.deep_view()),
    {
        self.inner.command = Some(command);
    }
}

impl TCPSocketAction {
    #[verifier(external_body)]
    pub fn set_host(&mut self, host: String)
        ensures self@ == old(self)@.with_host(host@),
    {
        self.inner.host = Some(host);
    }

    #[verifier(external_body)]
    pub fn set_port(&mut self, port: i32)
        ensures self@ == old(self)@.with_port(port as int),
    {
        self.inner.port = k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(port);
    }
}

impl Lifecycle {
    #[verifier(external_body)]
    pub fn set_pre_stop(&mut self, handler: LifecycleHandler)
        ensures self@ == old(self)@.with_pre_stop(handler@),
    {
        self.inner.pre_stop = Some(handler.into_kube());
    }
}

impl LifecycleHandler {
    #[verifier(external_body)]
    pub fn set_exec(&mut self, exec: ExecAction)
        ensures self@ == old(self)@.with_exec(exec@),
    {
        self.inner.exec = Some(exec.into_kube());
    }
}

impl EnvVar {
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
        ensures self@ == old(self)@.with_name(name@),
    {
        self.inner.name = name;
    }

    #[verifier(external_body)]
    pub fn set_value(&mut self, value: String)
        ensures self@ == old(self)@.with_value(value@),
    {
        self.inner.value = Some(value)
    }

    #[verifier(external_body)]
    pub fn set_value_from(&mut self, value_from: EnvVarSource)
        ensures self@ == old(self)@.with_value_from(value_from@),
    {
        self.inner.value_from = Some(value_from.into_kube())
    }
}

impl EnvVarSource {
    pub fn new_with_field_ref(field_ref: ObjectFieldSelector) -> (env_var_source: EnvVarSource)
        ensures env_var_source@ == EnvVarSourceView::default().with_field_ref(field_ref@)
    {
        let mut source = EnvVarSource::default();
        source.set_field_ref(field_ref);
        source
    }

    #[verifier(external_body)]
    pub fn set_field_ref(&mut self, field_ref: ObjectFieldSelector)
        ensures self@ == old(self)@.with_field_ref(field_ref@),
    {
        self.inner.field_ref = Some(field_ref.into_kube());
    }
}

}
