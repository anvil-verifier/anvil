// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::resource::*;
use crate::kubernetes_api_objects::resource_requirements::*;
use crate::pervasive_ext::string_view::*;
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

    // Methods for the fields that do not appear in spec

    #[verifier(external_body)]
    pub fn set_command(&mut self, command: Vec<String>)
        ensures
            self@ == old(self)@,
    {
        self.inner.command = Some(
            command.into_iter().map(|c: String| c.into_rust_string()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_image_pull_policy(&mut self, image_pull_policy: String)
        ensures
            self@ == old(self)@,
    {
        self.inner.image_pull_policy = Some(image_pull_policy.into_rust_string())
    }

    #[verifier(external_body)]
    pub fn set_liveness_probe(&mut self, liveness_probe: Probe)
        ensures
            self@ == old(self)@,
    {
        self.inner.liveness_probe = Some(liveness_probe.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_readiness_probe(&mut self, readiness_probe: Probe)
        ensures
            self@ == old(self)@,
    {
        self.inner.readiness_probe = Some(readiness_probe.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_env(&mut self, env: Vec<EnvVar>)
        ensures
            self@ == old(self)@,
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
    pub fn set_exec(&mut self, commands: Vec<String>)
        ensures
            self@ == old(self)@.set_exec(commands@.map_values(|c: String| c@)),
    {
        self.inner.exec = Some(
            // TODO: wrap a resource wrapper for ExecAction
            deps_hack::k8s_openapi::api::core::v1::ExecAction {
                command: Some(commands.into_iter().map(|c: String| c.into_rust_string()).collect())
            }
        );
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
    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::EnvVar) -> EnvVar {
        EnvVar { inner: inner }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::EnvVar {
        self.inner
    }
}

pub struct ContainerView {
    pub image: Option<StringView>,
    pub name: StringView,
    pub ports: Option<Seq<ContainerPortView>>,
    pub volume_mounts: Option<Seq<VolumeMountView>>,
    pub lifecycle: Option<LifecycleView>,
    pub resources: Option<ResourceRequirementsView>,
}

impl ContainerView {
    pub open spec fn default() -> ContainerView {
        ContainerView {
            image: None,
            name: new_strlit("")@,
            ports: None,
            volume_mounts: None,
            lifecycle: None,
            resources: None,
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
    pub exec_: Option<Seq<StringView>>,
}

impl LifecycleHandlerView {
    pub open spec fn default() -> LifecycleHandlerView {
        LifecycleHandlerView {
            exec_: None,
        }
    }

    pub open spec fn set_exec(self, commands: Seq<StringView>) -> LifecycleHandlerView {
        // TODO: implement a ghost type for ExecAction
        LifecycleHandlerView {
            exec_: Some(commands),
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

}
