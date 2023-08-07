// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::kubernetes_api_objects::resource_requirements::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

/// Pod is a type of API object used for grouping one or more containers that share storage and network resources.
/// This is the smallest deployable unit in Kubernetes.
///
/// You can specify the Container(s), including the images and commands, and the Volume(s),
/// such as a ConfigMap or a Secret, in the specification of a Pod (i.e., PodSpec).
///
/// This definition is a wrapper of Pod defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/pod.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/workloads/pods/.

#[verifier(external_body)]
pub struct Pod {
    inner: deps_hack::k8s_openapi::api::core::v1::Pod,
}

impl Pod {
    pub spec fn view(&self) -> PodView;

    #[verifier(external_body)]
    pub fn default() -> (pod: Pod)
        ensures
            pod@ == PodView::default(),
    {
        Pod {
            inner: deps_hack::k8s_openapi::api::core::v1::Pod::default(),
        }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: Option<PodSpec>)
        ensures
            self@.spec.is_Some() == spec.is_Some(),
            spec.is_Some() ==> spec.get_Some_0()@ == self@.spec.get_Some_0(),
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn set_metadata(&mut self, metadata: ObjectMeta)
        ensures
            self@ == old(self)@.set_metadata(metadata@),
    {
        self.inner.metadata = metadata.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: PodSpec)
        ensures
            self@ == old(self)@.set_spec(spec@),
    {
        self.inner.spec = Some(spec.into_kube());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Pod {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == PodView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::core::v1::Pod>(&()))
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    /// Convert a DynamicObject to a Pod
    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (res: Result<Pod, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == PodView::from_dynamic_object(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == PodView::from_dynamic_object(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::core::v1::Pod>();
        if parse_result.is_ok() {
            let res = Pod { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

#[verifier(external_body)]
pub struct PodSpec {
    inner: deps_hack::k8s_openapi::api::core::v1::PodSpec,
}

impl PodSpec {
    pub spec fn view(&self) -> PodSpecView;

    #[verifier(external_body)]
    pub fn default() -> (pod_spec: PodSpec)
        ensures
            pod_spec@ == PodSpecView::default(),
    {
        PodSpec {
            inner: deps_hack::k8s_openapi::api::core::v1::PodSpec::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_containers(&mut self, containers: Vec<Container>)
        ensures
            self@ == old(self)@.set_containers(containers@.map_values(|container: Container| container@)),
    {
        self.inner.containers = containers.into_iter().map(|container: Container| container.into_kube()).collect()
    }

    #[verifier(external_body)]
    pub fn set_volumes(&mut self, volumes: Vec<Volume>)
        ensures
            self@ == old(self)@.set_volumes(volumes@.map_values(|vol: Volume| vol@)),
    {
        self.inner.volumes = Some(volumes.into_iter().map(|vol: Volume| vol.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_init_containers(&mut self, init_containers: Vec<Container>)
        ensures
            self@ == old(self)@.set_init_containers(init_containers@.map_values(|container: Container| container@)),
    {
        self.inner.init_containers = Some(init_containers.into_iter().map(|container: Container| container.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_service_account_name(&mut self, service_account: String)
        ensures
            self@ == old(self)@.set_service_account_name(service_account@),
    {
        self.inner.service_account_name = Some(service_account.into_rust_string())
    }

    #[verifier(external_body)]
    pub fn set_tolerations(&mut self, tolerations: Vec<Toleration>)
        ensures
            self@ == old(self)@,
    {
        self.inner.tolerations = Some(
            tolerations.into_iter().map(|t: Toleration| t.into_kube()).collect()
        )
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::PodSpec {
        self.inner
    }
}

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
pub struct Toleration {
    inner: deps_hack::k8s_openapi::api::core::v1::Toleration,
}

impl Toleration {
    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::Toleration) -> Toleration {
        Toleration { inner: inner }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Toleration {
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
pub struct Volume {
    inner: deps_hack::k8s_openapi::api::core::v1::Volume,
}

impl Volume {
    pub spec fn view(&self) -> VolumeView;

    #[verifier(external_body)]
    pub fn default() -> (volume: Volume)
        ensures
            volume@ == VolumeView::default(),
    {
        Volume {
            inner: deps_hack::k8s_openapi::api::core::v1::Volume::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = name.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_host_path(&mut self, host_path: HostPathVolumeSource)
        ensures
            self@ == old(self)@.set_host_path(host_path@),
    {
        self.inner.host_path = Some(host_path.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_config_map(&mut self, config_map: ConfigMapVolumeSource)
        ensures
            self@ == old(self)@.set_config_map(config_map@),
    {
        self.inner.config_map = Some(config_map.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_projected(&mut self, projected: ProjectedVolumeSource)
        ensures
            self@ == old(self)@.set_projected(projected@),
    {
        self.inner.projected = Some(projected.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_secret(&mut self, secret: SecretVolumeSource)
        ensures
            self@ == old(self)@.set_secret(secret@),
    {
        self.inner.secret = Some(secret.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_downward_api(&mut self, downward_api: DownwardAPIVolumeSource)
        ensures
            self@ == old(self)@.set_downward_api(downward_api@),
    {
        self.inner.downward_api = Some(downward_api.into_kube());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Volume {
        self.inner
    }

    /// Methods for the fields that Anvil currently does not reason about

    #[verifier(external_body)]
    pub fn set_empty_dir(&mut self)
        ensures
            self@ == old(self)@,
    {
        self.inner.empty_dir = Some(deps_hack::k8s_openapi::api::core::v1::EmptyDirVolumeSource{
            ..deps_hack::k8s_openapi::api::core::v1::EmptyDirVolumeSource::default()
        });
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
pub struct HostPathVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::HostPathVolumeSource,
}

impl HostPathVolumeSource {
    pub spec fn view(&self) -> HostPathVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (host_path_volume_source: HostPathVolumeSource)
        ensures
            host_path_volume_source@ == HostPathVolumeSourceView::default(),
    {
        HostPathVolumeSource {
            inner: deps_hack::k8s_openapi::api::core::v1::HostPathVolumeSource::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_path(&mut self, path: String)
        ensures
            self@ == old(self)@.set_path(path@),
    {
        self.inner.path = path.into_rust_string();
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::HostPathVolumeSource {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ConfigMapVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::ConfigMapVolumeSource,
}

impl ConfigMapVolumeSource {
    pub spec fn view(&self) -> ConfigMapVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (config_map_volume_source: ConfigMapVolumeSource)
        ensures
            config_map_volume_source@ == ConfigMapVolumeSourceView::default(),
    {
        ConfigMapVolumeSource {
            inner: deps_hack::k8s_openapi::api::core::v1::ConfigMapVolumeSource::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = Some(name.into_rust_string());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ConfigMapVolumeSource {
        self.inner
    }
}

#[verifier(external_body)]
pub struct SecretVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::SecretVolumeSource,
}

impl SecretVolumeSource {
    pub spec fn view(&self) -> SecretVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (secret_volume_source: SecretVolumeSource)
        ensures
            secret_volume_source@ == SecretVolumeSourceView::default(),
    {
        SecretVolumeSource {
            inner: deps_hack::k8s_openapi::api::core::v1::SecretVolumeSource::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_secret_name(&mut self, secret_name: String)
        ensures
            self@ == old(self)@.set_secret_name(secret_name@),
    {
        self.inner.secret_name = Some(secret_name.into_rust_string());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::SecretVolumeSource {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ProjectedVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::ProjectedVolumeSource,
}

impl ProjectedVolumeSource {
    pub spec fn view(&self) -> ProjectedVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (projected_volume_source: ProjectedVolumeSource)
        ensures
            projected_volume_source@ == ProjectedVolumeSourceView::default(),
    {
        ProjectedVolumeSource {
            inner: deps_hack::k8s_openapi::api::core::v1::ProjectedVolumeSource::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_sources(&mut self, sources: Vec<VolumeProjection>)
        ensures
            self@ == old(self)@.set_sources(sources@.map_values(|v: VolumeProjection| v@)),
    {
        self.inner.sources = Some(
            sources.into_iter().map(|v: VolumeProjection| v.into_kube()).collect()
        );
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ProjectedVolumeSource {
        self.inner
    }
}

#[verifier(external_body)]
pub struct VolumeProjection {
    inner: deps_hack::k8s_openapi::api::core::v1::VolumeProjection,
}

impl VolumeProjection {
    pub spec fn view(&self) -> VolumeProjectionView;

    #[verifier(external_body)]
    pub fn default() -> (volume_projection: VolumeProjection)
        ensures
            volume_projection@ == VolumeProjectionView::default(),
    {
        VolumeProjection {
            inner: deps_hack::k8s_openapi::api::core::v1::VolumeProjection::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_config_map(&mut self, config_map: ConfigMapProjection)
        ensures
            self@ == old(self)@.set_config_map(config_map@),
    {
        self.inner.config_map = Some(config_map.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_secret(&mut self, secret: SecretProjection)
        ensures
            self@ == old(self)@.set_secret(secret@),
    {
        self.inner.secret = Some(secret.into_kube());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::VolumeProjection {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ConfigMapProjection {
    inner: deps_hack::k8s_openapi::api::core::v1::ConfigMapProjection,
}

impl ConfigMapProjection {
    pub spec fn view(&self) -> ConfigMapProjectionView;

    #[verifier(external_body)]
    pub fn default() -> (config_map_projection: ConfigMapProjection)
        ensures
            config_map_projection@ == ConfigMapProjectionView::default(),
    {
        ConfigMapProjection {
            inner: deps_hack::k8s_openapi::api::core::v1::ConfigMapProjection::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = Some(name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_items(&mut self, items: Vec<KeyToPath>)
        ensures
            self@ == old(self)@.set_items(items@.map_values(|v: KeyToPath| v@)),
    {
        self.inner.items = Some(
            items.into_iter().map(|v: KeyToPath| v.into_kube()).collect()
        );
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ConfigMapProjection {
        self.inner
    }
}

#[verifier(external_body)]
pub struct SecretProjection {
    inner: deps_hack::k8s_openapi::api::core::v1::SecretProjection,
}

impl SecretProjection {
    pub spec fn view(&self) -> SecretProjectionView;

    #[verifier(external_body)]
    pub fn default() -> (secret_projection: SecretProjection)
        ensures
            secret_projection@ == SecretProjectionView::default(),
    {
        SecretProjection {
            inner: deps_hack::k8s_openapi::api::core::v1::SecretProjection::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = Some(name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_items(&mut self, items: Vec<KeyToPath>)
        ensures
            self@ == old(self)@.set_items(items@.map_values(|v: KeyToPath| v@)),
    {
        self.inner.items = Some(
            items.into_iter().map(|v: KeyToPath| v.into_kube()).collect()
        );
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::SecretProjection {
        self.inner
    }
}

#[verifier(external_body)]
pub struct KeyToPath {
    inner: deps_hack::k8s_openapi::api::core::v1::KeyToPath,
}

impl KeyToPath {
    pub spec fn view(&self) -> KeyToPathView;

    #[verifier(external_body)]
    pub fn default() -> (key_to_path: KeyToPath)
        ensures
            key_to_path@ == KeyToPathView::default(),
    {
        KeyToPath {
            inner: deps_hack::k8s_openapi::api::core::v1::KeyToPath::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_key(&mut self, key: String)
        ensures
            self@ == old(self)@.set_key(key@),
    {
        self.inner.key = key.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_path(&mut self, path: String)
        ensures
            self@ == old(self)@.set_path(path@),
    {
        self.inner.path = path.into_rust_string();
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::KeyToPath {
        self.inner
    }
}

#[verifier(external_body)]
pub struct DownwardAPIVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeSource,
}

impl DownwardAPIVolumeSource {
    pub spec fn view(&self) -> DownwardAPIVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (downward_api_volume_source: DownwardAPIVolumeSource)
        ensures
            downward_api_volume_source@ == DownwardAPIVolumeSourceView::default(),
    {
        DownwardAPIVolumeSource {
            inner: deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeSource::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_items(&mut self, items: Vec<DownwardAPIVolumeFile>)
        ensures
            self@ == old(self)@.set_items(items@.map_values(|v: DownwardAPIVolumeFile| v@)),
    {
        self.inner.items = Some(
            items.into_iter().map(|v: DownwardAPIVolumeFile| v.into_kube()).collect()
        );
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeSource {
        self.inner
    }
}

#[verifier(external_body)]
pub struct DownwardAPIVolumeFile {
    inner: deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeFile,
}

impl DownwardAPIVolumeFile {
    pub spec fn view(&self) -> DownwardAPIVolumeFileView;

    #[verifier(external_body)]
    pub fn default() -> (downward_api_volume_file: DownwardAPIVolumeFile)
        ensures
            downward_api_volume_file@ == DownwardAPIVolumeFileView::default(),
    {
        DownwardAPIVolumeFile {
            inner: deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeFile::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_field_ref(&mut self, field_ref: ObjectFieldSelector)
        ensures
            self@ == old(self)@.set_field_ref(field_ref@),
    {
        self.inner.field_ref = Some(field_ref.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_path(&mut self, path: String)
        ensures
            self@ == old(self)@.set_path(path@),
    {
        self.inner.path = path.into_rust_string();
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeFile {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ObjectFieldSelector {
    inner: deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector,
}

impl ObjectFieldSelector {
    pub spec fn view(&self) -> ObjectFieldSelectorView;

    #[verifier(external_body)]
    pub fn default() -> (object_field_selector: ObjectFieldSelector)
        ensures
            object_field_selector@ == ObjectFieldSelectorView::default(),
    {
        ObjectFieldSelector {
            inner: deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_field_path(&mut self, field_path: String)
        ensures
            self@ == old(self)@.set_field_path(field_path@),
    {
        self.inner.field_path = field_path.into_rust_string();
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector {
        self.inner
    }
}

/// PodView is the ghost type of Pod.
/// It is supposed to be used in spec and proof code.

pub struct PodView {
    pub metadata: ObjectMetaView,
    pub spec: Option<PodSpecView>,
}

impl PodView {
    pub open spec fn default() -> PodView {
        PodView {
            metadata: ObjectMetaView::default(),
            spec: None,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> PodView {
        PodView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_spec(self, spec: PodSpecView) -> PodView {
        PodView {
            spec: Some(spec),
            ..self
        }
    }
}

impl ResourceView for PodView {
    type Spec = Option<PodSpecView>;

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::PodKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> Option<PodSpecView> {
        self.spec
    }

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: PodView::marshal_spec(self.spec),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<PodView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !PodView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(PodView {
                metadata: obj.metadata,
                spec: PodView::unmarshal_spec(obj.spec).get_Ok_0(),
            })
        }
    }

    proof fn to_dynamic_preserves_integrity() {
        PodView::spec_integrity_is_preserved_by_marshal();
    }

    proof fn from_dynamic_preserves_metadata() {}

    proof fn from_dynamic_preserves_kind() {}

    closed spec fn marshal_spec(s: Option<PodSpecView>) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<Option<PodSpecView>, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn spec_integrity_is_preserved_by_marshal(){}

    open spec fn rule(obj: PodView) -> bool {
        true
    }

    open spec fn transition_rule(new_obj: PodView, old_obj: PodView) -> bool {
        true
    }
}

pub struct PodSpecView {
    pub containers: Seq<ContainerView>,
    pub volumes: Option<Seq<VolumeView>>,
    pub init_containers: Option<Seq<ContainerView>>,
    pub service_account_name: Option<StringView>,
}

impl PodSpecView {
    pub open spec fn default() -> PodSpecView {
        PodSpecView {
            containers: Seq::empty(),
            volumes: None,
            init_containers: None,
            service_account_name: None,
        }
    }

    pub open spec fn set_containers(self, containers: Seq<ContainerView>) -> PodSpecView {
        PodSpecView {
            containers: containers,
            ..self
        }
    }

    pub open spec fn set_volumes(self, volumes: Seq<VolumeView>) -> PodSpecView {
        PodSpecView {
            volumes: Some(volumes),
            ..self
        }
    }

    pub open spec fn set_init_containers(self, init_containers: Seq<ContainerView>) -> PodSpecView {
        PodSpecView {
            init_containers: Some(init_containers),
            ..self
        }
    }

    pub open spec fn set_service_account_name(self, service_account_name: StringView) -> PodSpecView {
        PodSpecView {
            service_account_name: Some(service_account_name),
            ..self
        }
    }
}

impl Marshalable for PodSpecView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
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

impl Marshalable for ContainerView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
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

impl Marshalable for ContainerPortView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
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

impl Marshalable for VolumeMountView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

pub struct VolumeView {
    pub host_path: Option<HostPathVolumeSourceView>,
    pub config_map: Option<ConfigMapVolumeSourceView>,
    pub name: StringView,
    pub projected: Option<ProjectedVolumeSourceView>,
    pub secret: Option<SecretVolumeSourceView>,
    pub downward_api: Option<DownwardAPIVolumeSourceView>,
}

impl VolumeView {
    pub open spec fn default() -> VolumeView {
        VolumeView {
            name: new_strlit("")@,
            config_map: None,
            host_path: None,
            projected: None,
            secret: None,
            downward_api: None,
        }
    }

    pub open spec fn set_host_path(self, host_path: HostPathVolumeSourceView) -> VolumeView {
        VolumeView {
            host_path: Some(host_path),
            ..self
        }
    }

    pub open spec fn set_config_map(self, config_map: ConfigMapVolumeSourceView) -> VolumeView {
        VolumeView {
            config_map: Some(config_map),
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> VolumeView {
        VolumeView {
            name: name,
            ..self
        }
    }

    pub open spec fn set_projected(self, projected: ProjectedVolumeSourceView) -> VolumeView {
        VolumeView {
            projected: Some(projected),
            ..self
        }
    }

    pub open spec fn set_secret(self, secret: SecretVolumeSourceView) -> VolumeView  {
        VolumeView {
            secret: Some(secret),
            ..self
        }
    }

    pub open spec fn set_downward_api(self, downward_api: DownwardAPIVolumeSourceView) -> VolumeView {
        VolumeView {
            downward_api: Some(downward_api),
            ..self
        }
    }
}

impl Marshalable for VolumeView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

pub struct HostPathVolumeSourceView {
    pub path: StringView,
}

impl HostPathVolumeSourceView {
    pub open spec fn default() -> HostPathVolumeSourceView {
        HostPathVolumeSourceView {
            path: new_strlit("")@,
        }
    }

    pub open spec fn set_path(self, path: StringView) -> HostPathVolumeSourceView {
        HostPathVolumeSourceView {
            path: path,
            ..self
        }
    }
}

pub struct ConfigMapVolumeSourceView {
    pub name: Option<StringView>,
}

impl ConfigMapVolumeSourceView {
    pub open spec fn default() -> ConfigMapVolumeSourceView {
        ConfigMapVolumeSourceView {
            name: None,
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ConfigMapVolumeSourceView {
        ConfigMapVolumeSourceView {
            name: Some(name),
            ..self
        }
    }
}

impl Marshalable for ConfigMapVolumeSourceView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

pub struct SecretVolumeSourceView {
    pub secret_name: Option<StringView>,
}

impl SecretVolumeSourceView {
    pub open spec fn default() -> SecretVolumeSourceView {
        SecretVolumeSourceView {
            secret_name: None,
        }
    }

    pub open spec fn set_secret_name(self, secret_name: StringView) -> SecretVolumeSourceView {
        SecretVolumeSourceView {
            secret_name: Some(secret_name),
            ..self
        }
    }
}

impl Marshalable for SecretVolumeSourceView {
    open spec fn marshal(self) -> Value;

    open spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

pub struct ProjectedVolumeSourceView {
    pub sources: Option<Seq<VolumeProjectionView>>,
}

impl ProjectedVolumeSourceView {
    pub open spec fn default() -> ProjectedVolumeSourceView {
        ProjectedVolumeSourceView {
            sources: None,
        }
    }

    pub open spec fn set_sources(self, sources: Seq<VolumeProjectionView>) -> ProjectedVolumeSourceView {
        ProjectedVolumeSourceView {
            sources: Some(sources),
            ..self
        }
    }
}

impl Marshalable for ProjectedVolumeSourceView{
    open spec fn marshal(self) -> Value;

    open spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}


pub struct VolumeProjectionView {
    pub config_map: Option<ConfigMapProjectionView>,
    pub secret: Option<SecretProjectionView>,
}

impl VolumeProjectionView {
    pub open spec fn default() -> VolumeProjectionView {
        VolumeProjectionView {
            config_map: None,
            secret: None,
        }
    }

    pub open spec fn set_config_map(self, config_map: ConfigMapProjectionView) -> VolumeProjectionView {
        VolumeProjectionView {
            config_map: Some(config_map),
            ..self
        }
    }

    pub open spec fn set_secret(self, secret: SecretProjectionView) -> VolumeProjectionView {
        VolumeProjectionView {
            secret: Some(secret),
            ..self
        }
    }

}

impl Marshalable for VolumeProjectionView {
    open spec fn marshal(self) -> Value;

    open spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}





pub struct ConfigMapProjectionView {
    pub items: Option<Seq<KeyToPathView>>,
    pub name: Option<StringView>
}

impl ConfigMapProjectionView {
    pub open spec fn default() -> ConfigMapProjectionView {
        ConfigMapProjectionView {
            items: None,
            name: None,
        }
    }

    pub open spec fn set_items(self, items: Seq<KeyToPathView>) -> ConfigMapProjectionView {
        ConfigMapProjectionView {
            items: Some(items),
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ConfigMapProjectionView {
        ConfigMapProjectionView {
            name: Some(name),
            ..self
        }
    }
}

impl Marshalable for ConfigMapProjectionView {
    open spec fn marshal(self) -> Value;

    open spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}





pub struct SecretProjectionView {
    pub items: Option<Seq<KeyToPathView>>,
    pub name: Option<StringView>
}

impl SecretProjectionView {
    pub open spec fn default() -> SecretProjectionView {
        SecretProjectionView {
            items: None,
            name: None,
        }
    }

    pub open spec fn set_items(self, items: Seq<KeyToPathView>) -> SecretProjectionView {
        SecretProjectionView {
            items: Some(items),
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> SecretProjectionView {
        SecretProjectionView {
            name: Some(name),
            ..self
        }
    }
}

impl Marshalable for SecretProjectionView {
    open spec fn marshal(self) -> Value;

    open spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

pub struct KeyToPathView {
    pub key: StringView,
    pub path: StringView,
}

impl KeyToPathView {
    pub open spec fn default() -> KeyToPathView {
        KeyToPathView {
            key: new_strlit("")@,
            path: new_strlit("")@,
        }
    }

    pub open spec fn set_key(self, key: StringView) -> KeyToPathView {
        KeyToPathView {
            key,
            ..self
        }
    }

    pub open spec fn set_path(self, path: StringView) -> KeyToPathView {
        KeyToPathView {
            path,
            ..self
        }
    }
}

impl Marshalable for KeyToPathView {
    open spec fn marshal(self) -> Value;

    open spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

pub struct DownwardAPIVolumeSourceView {
    pub items: Option<Seq<DownwardAPIVolumeFileView>>,
}
impl DownwardAPIVolumeSourceView {
    pub open spec fn default() -> DownwardAPIVolumeSourceView {
        DownwardAPIVolumeSourceView {
            items: None,
        }
    }

    pub open spec fn set_items(self, items: Seq<DownwardAPIVolumeFileView>) -> DownwardAPIVolumeSourceView {
        DownwardAPIVolumeSourceView {
            items: Some(items),
            ..self
        }
    }
}

impl Marshalable for DownwardAPIVolumeSourceView {
    open spec fn marshal(self) -> Value;

    open spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

pub struct DownwardAPIVolumeFileView {
    pub field_ref: Option<ObjectFieldSelectorView>,
    pub path: StringView,
}
impl DownwardAPIVolumeFileView {
    pub open spec fn default() -> DownwardAPIVolumeFileView {
        DownwardAPIVolumeFileView {
            field_ref: None,
            path: new_strlit("")@,
        }
    }

    pub open spec fn set_field_ref(self, field_ref: ObjectFieldSelectorView) -> DownwardAPIVolumeFileView {
        DownwardAPIVolumeFileView {
            field_ref: Some(field_ref),
            ..self
        }
    }

    pub open spec fn set_path(self, path: StringView) -> DownwardAPIVolumeFileView {
        DownwardAPIVolumeFileView {
            path,
            ..self
        }
    }
}

impl Marshalable for DownwardAPIVolumeFileView {
    open spec fn marshal(self) -> Value;

    open spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

pub struct ObjectFieldSelectorView {
    pub field_path: StringView,
}
impl ObjectFieldSelectorView {
    pub open spec fn default() -> ObjectFieldSelectorView {
        ObjectFieldSelectorView {
            field_path: new_strlit("")@,
        }
    }

    pub open spec fn set_field_path(self, field_path: StringView) -> ObjectFieldSelectorView {
        ObjectFieldSelectorView {
            field_path,
            ..self
        }
    }
}

impl Marshalable for ObjectFieldSelectorView {
    open spec fn marshal(self) -> Value;

    open spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}


}
