// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;
use vstd::vec::*;

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
        todo!()
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
        self.inner.spec = std::option::Option::Some(spec.into_kube());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Pod {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == Kind::CustomResourceKind,
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
            Result::Ok(res)
        } else {
            Result::Err(ParseDynamicObjectError::ExecError)
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
        self.inner.containers = containers.vec.into_iter().map(|container: Container| container.into_kube()).collect()
    }

    #[verifier(external_body)]
    pub fn set_volumes(&mut self, volumes: Vec<Volume>)
        ensures
            self@ == old(self)@.set_volumes(volumes@.map_values(|vol: Volume| vol@)),
    {
        self.inner.volumes = std::option::Option::Some(volumes.vec.into_iter().map(|vol: Volume| vol.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_init_containers(&mut self, init_containers: Vec<Container>)
        ensures
            self@ == old(self)@.set_init_containers(init_containers@.map_values(|container: Container| container@)),
    {
        self.inner.init_containers = std::option::Option::Some(init_containers.vec.into_iter().map(|container: Container| container.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_service_account_name(&mut self, service_account: String)
        ensures
            self@ == old(self)@.set_service_account_name(service_account@),
    {
        self.inner.service_account_name = std::option::Option::Some(service_account.into_rust_string())
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
        self.inner.image = std::option::Option::Some(image.into_rust_string())
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
        self.inner.volume_mounts = std::option::Option::Some(
            volume_mounts.vec.into_iter().map(|mount: VolumeMount| mount.into_kube()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_ports(&mut self, ports: Vec<ContainerPort>)
        ensures
            self@ == old(self)@.set_ports(ports@.map_values(|port: ContainerPort| port@)),
    {
        self.inner.ports = std::option::Option::Some(
            ports.vec.into_iter().map(|port: ContainerPort| port.into_kube()).collect()
        )
    }

    /// Methods for the fields that Anvil currently does not reason about

    #[verifier(external_body)]
    pub fn set_command(&mut self, command: Vec<String>)
        ensures
            self@ == old(self)@,
    {
        self.inner.command = std::option::Option::Some(
            command.vec.into_iter().map(|c: String| c.into_rust_string()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_image_pull_policy(&mut self, image_pull_policy: String)
        ensures
            self@ == old(self)@,
    {
        self.inner.image_pull_policy = std::option::Option::Some(image_pull_policy.into_rust_string())
    }

    #[verifier(external_body)]
    pub fn set_liveness_probe(&mut self, liveness_probe: Probe)
        ensures
            self@ == old(self)@,
    {
        self.inner.liveness_probe = std::option::Option::Some(liveness_probe.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_readiness_probe(&mut self, readiness_probe: Probe)
        ensures
            self@ == old(self)@,
    {
        self.inner.readiness_probe = std::option::Option::Some(readiness_probe.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_env(&mut self, env: Vec<EnvVar>)
        ensures
            self@ == old(self)@,
    {
        self.inner.env = std::option::Option::Some(
            env.vec.into_iter().map(|e: EnvVar| e.into_kube()).collect()
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
        self.inner.name = std::option::Option::Some(name.into_rust_string());
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
    pub fn set_sub_path(&mut self, sub_path: String)
        ensures
            self@ == old(self)@.set_sub_path(sub_path@),
    {
        self.inner.sub_path = std::option::Option::Some(sub_path.into_rust_string());
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
    pub fn set_config_map(&mut self, config_map: ConfigMapVolumeSource)
        ensures
            self@ == old(self)@.set_config_map(config_map@),
    {
        self.inner.config_map = std::option::Option::Some(config_map.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_projected(&mut self, projected: ProjectedVolumeSource)
        ensures
            self@ == old(self)@.set_projected(projected@),
    {
        self.inner.projected = std::option::Option::Some(projected.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_secret(&mut self, secret: SecretVolumeSource)
        ensures
            self@ == old(self)@.set_secret(secret@),
    {
        self.inner.secret = std::option::Option::Some(secret.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_downward_api(&mut self, downward_api: DownwardAPIVolumeSource)
        ensures
            self@ == old(self)@.set_downward_api(downward_api@),
    {
        self.inner.downward_api = std::option::Option::Some(downward_api.into_kube());
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
        self.inner.empty_dir = std::option::Option::Some(deps_hack::k8s_openapi::api::core::v1::EmptyDirVolumeSource{
            ..deps_hack::k8s_openapi::api::core::v1::EmptyDirVolumeSource::default()
        });
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
        self.inner.name = std::option::Option::Some(name.into_rust_string());
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
        self.inner.secret_name = std::option::Option::Some(secret_name.into_rust_string());
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
        self.inner.sources = std::option::Option::Some(
            sources.vec.into_iter().map(|v: VolumeProjection| v.into_kube()).collect()
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
        self.inner.config_map = std::option::Option::Some(config_map.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_secret(&mut self, secret: SecretProjection)
        ensures
            self@ == old(self)@.set_secret(secret@),
    {
        self.inner.secret = std::option::Option::Some(secret.into_kube());
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
        self.inner.name = std::option::Option::Some(name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_items(&mut self, items: Vec<KeyToPath>)
        ensures
            self@ == old(self)@.set_items(items@.map_values(|v: KeyToPath| v@)),
    {
        self.inner.items = std::option::Option::Some(
            items.vec.into_iter().map(|v: KeyToPath| v.into_kube()).collect()
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
        self.inner.name = std::option::Option::Some(name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_items(&mut self, items: Vec<KeyToPath>)
        ensures
            self@ == old(self)@.set_items(items@.map_values(|v: KeyToPath| v@)),
    {
        self.inner.items = std::option::Option::Some(
            items.vec.into_iter().map(|v: KeyToPath| v.into_kube()).collect()
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
        self.inner.items = std::option::Option::Some(
            items.vec.into_iter().map(|v: DownwardAPIVolumeFile| v.into_kube()).collect()
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
        self.inner.field_ref = std::option::Option::Some(field_ref.into_kube());
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
            spec: Option::None,
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
            spec: Option::Some(spec),
            ..self
        }
    }

    pub closed spec fn marshal_spec(s: Option<PodSpecView>) -> Value;

    pub closed spec fn unmarshal_spec(v: Value) -> Result<Option<PodSpecView>, ParseDynamicObjectError>;

    #[verifier(external_body)]
    pub proof fn spec_integrity_is_preserved_by_marshal()
        ensures
            forall |s: Option<PodSpecView>|
                Self::unmarshal_spec(#[trigger] Self::marshal_spec(s)).is_Ok()
                && s == Self::unmarshal_spec(Self::marshal_spec(s)).get_Ok_0() {}
}

impl ResourceView for PodView {
    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind(self) -> Kind {
        Kind::PodKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: self.kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: self.kind(),
            metadata: self.metadata,
            data: PodView::marshal_spec(self.spec),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<PodView, ParseDynamicObjectError> {
        if !PodView::unmarshal_spec(obj.data).is_Ok() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Result::Ok(PodView {
                metadata: obj.metadata,
                spec: PodView::unmarshal_spec(obj.data).get_Ok_0(),
            })
        }
    }

    proof fn to_dynamic_preserves_integrity() {
        PodView::spec_integrity_is_preserved_by_marshal();
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
            volumes: Option::None,
            init_containers: Option::None,
            service_account_name: Option::None,
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
            volumes: Option::Some(volumes),
            ..self
        }
    }

    pub open spec fn set_init_containers(self, init_containers: Seq<ContainerView>) -> PodSpecView {
        PodSpecView {
            init_containers: Option::Some(init_containers),
            ..self
        }
    }

    pub open spec fn set_service_account_name(self, service_account_name: StringView) -> PodSpecView {
        PodSpecView {
            service_account_name: Option::Some(service_account_name),
            ..self
        }
    }

    pub open spec fn init_containers_field() -> nat {2}

    pub open spec fn service_account_name_field() -> nat {3}
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
}

impl ContainerView {
    pub open spec fn default() -> ContainerView {
        ContainerView {
            image: Option::None,
            name: new_strlit("")@,
            ports: Option::None,
            volume_mounts: Option::None,
        }
    }

    pub open spec fn set_image(self, image: StringView) -> ContainerView {
        ContainerView {
            image: Option::Some(image),
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
            ports: Option::Some(ports),
            ..self
        }
    }

    pub open spec fn set_volume_mounts(self, volume_mounts: Seq<VolumeMountView>) -> ContainerView {
        ContainerView {
            volume_mounts: Option::Some(volume_mounts),
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

pub struct ContainerPortView {
    pub container_port: int,
    pub name: Option<StringView>,
}

impl ContainerPortView {
    pub open spec fn default() -> ContainerPortView {
        ContainerPortView {
            container_port: 0, // TODO: is this the correct default value?
            name: Option::None,
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
            name: Option::Some(name),
            ..self
        }
    }

    pub open spec fn container_port_field() -> nat {0}

    pub open spec fn name_field() -> nat {1}
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
    pub sub_path: Option<StringView>,
}

impl VolumeMountView {
    pub open spec fn default() -> VolumeMountView {
        VolumeMountView {
            mount_path: new_strlit("")@,
            name: new_strlit("")@,
            sub_path: Option::None,
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

    pub open spec fn set_sub_path(self, sub_path: StringView) -> VolumeMountView {
        VolumeMountView {
            sub_path: Option::Some(sub_path),
            ..self
        }
    }

    pub open spec fn sub_path_field() -> nat {2}
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
            config_map: Option::None,
            projected: Option::None,
            secret: Option::None,
            downward_api: Option::None,
        }
    }

    pub open spec fn set_config_map(self, config_map: ConfigMapVolumeSourceView) -> VolumeView {
        VolumeView {
            config_map: Option::Some(config_map),
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
            projected: Option::Some(projected),
            ..self
        }
    }

    pub open spec fn set_secret(self, secret: SecretVolumeSourceView) -> VolumeView  {
        VolumeView {
            secret: Option::Some(secret),
            ..self
        }
    }

    pub open spec fn set_downward_api(self, downward_api: DownwardAPIVolumeSourceView) -> VolumeView {
        VolumeView {
            downward_api: Option::Some(downward_api),
            ..self
        }
    }

    pub open spec fn projected_field() -> nat {2}

    pub open spec fn secret_field() -> nat {3}

    pub open spec fn downward_api_field() -> nat {4}
}


impl Marshalable for VolumeView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

pub struct ConfigMapVolumeSourceView {
    pub name: Option<StringView>,
}

impl ConfigMapVolumeSourceView {
    pub open spec fn default() -> ConfigMapVolumeSourceView {
        ConfigMapVolumeSourceView {
            name: Option::None,
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ConfigMapVolumeSourceView {
        ConfigMapVolumeSourceView {
            name: Option::Some(name),
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
            secret_name: Option::None,
        }
    }

    pub open spec fn set_secret_name(self, secret_name: StringView) -> SecretVolumeSourceView {
        SecretVolumeSourceView {
            secret_name: Option::Some(secret_name),
            ..self
        }
    }

    pub open spec fn secret_name_field() -> nat {0}
}

impl Marshalable for SecretVolumeSourceView {
    open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::secret_name_field(), if self.secret_name.is_None() { Value::Null } else {
                    Value::String(self.secret_name.get_Some_0())
                })
        )
    }

    open spec fn unmarshal(value: Value) -> Self {
        SecretVolumeSourceView {
            secret_name: if value.get_Object_0()[Self::secret_name_field()].is_Null() { Option::None } else {
                Option::Some(value.get_Object_0()[Self::secret_name_field()].get_String_0())
            },
        }
    }

    proof fn marshal_preserves_integrity() {}
}



pub struct ProjectedVolumeSourceView {
    pub sources: Option<Seq<VolumeProjectionView>>,
}

impl ProjectedVolumeSourceView {
    pub open spec fn default() -> ProjectedVolumeSourceView {
        ProjectedVolumeSourceView {
            sources: Option::None,
        }
    }

    pub open spec fn set_sources(self, sources: Seq<VolumeProjectionView>) -> ProjectedVolumeSourceView {
        ProjectedVolumeSourceView {
            sources: Option::Some(sources),
            ..self
        }
    }

    pub open spec fn sources_field() -> nat {0}
}

impl Marshalable for ProjectedVolumeSourceView{
    open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::sources_field(), if self.sources.is_None() { Value::Null } else {
                    Value::Array(self.sources.get_Some_0().map_values(|x: VolumeProjectionView| x.marshal()))
                })
        )
    }

    open spec fn unmarshal(value: Value) -> Self {
        ProjectedVolumeSourceView {
            sources: if value.get_Object_0()[Self::sources_field()].is_Null() { Option::None } else {
                Option::Some(value.get_Object_0()[Self::sources_field()].get_Array_0().map_values(|x| VolumeProjectionView::unmarshal(x)))
            },
        }
    }

    proof fn marshal_preserves_integrity() {
        assert forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()) by {
            if o.sources.is_Some() {
                VolumeProjectionView::marshal_preserves_integrity();
                assert_seqs_equal!(o.sources.get_Some_0(), Self::unmarshal(o.marshal()).sources.get_Some_0());
            }
        }
    }
}


pub struct VolumeProjectionView {
    pub config_map: Option<ConfigMapProjectionView>,
    pub secret: Option<SecretProjectionView>,
}

impl VolumeProjectionView {
    pub open spec fn default() -> VolumeProjectionView {
        VolumeProjectionView {
            config_map: Option::None,
            secret: Option::None,
        }
    }

    pub open spec fn set_config_map(self, config_map: ConfigMapProjectionView) -> VolumeProjectionView {
        VolumeProjectionView {
            config_map: Option::Some(config_map),
            ..self
        }
    }

    pub open spec fn set_secret(self, secret: SecretProjectionView) -> VolumeProjectionView {
        VolumeProjectionView {
            secret: Option::Some(secret),
            ..self
        }
    }

    pub open spec fn config_map_field() -> nat {0}

    pub open spec fn secret_field() -> nat {1}
}

impl Marshalable for VolumeProjectionView {
    open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::config_map_field(), if self.config_map.is_None() { Value::Null } else {
                    self.config_map.get_Some_0().marshal()
                })
                .insert(Self::secret_field(), if self.secret.is_None() { Value::Null } else {
                    self.secret.get_Some_0().marshal()
                })
        )
    }

    open spec fn unmarshal(value: Value) -> Self {
        VolumeProjectionView {
            config_map: if value.get_Object_0()[Self::config_map_field()].is_Null() { Option::None } else {
                Option::Some(ConfigMapProjectionView::unmarshal(value.get_Object_0()[Self::config_map_field()]))
            },
            secret: if value.get_Object_0()[Self::secret_field()].is_Null() { Option::None } else {
                Option::Some(SecretProjectionView::unmarshal(value.get_Object_0()[Self::secret_field()]))
            },
        }
    }

    proof fn marshal_preserves_integrity() {
        ConfigMapProjectionView::marshal_preserves_integrity();
        SecretProjectionView::marshal_preserves_integrity();
    }
}





pub struct ConfigMapProjectionView {
    pub items: Option<Seq<KeyToPathView>>,
    pub name: Option<StringView>
}

impl ConfigMapProjectionView {
    pub open spec fn default() -> ConfigMapProjectionView {
        ConfigMapProjectionView {
            items: Option::None,
            name: Option::None,
        }
    }

    pub open spec fn set_items(self, items: Seq<KeyToPathView>) -> ConfigMapProjectionView {
        ConfigMapProjectionView {
            items: Option::Some(items),
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ConfigMapProjectionView {
        ConfigMapProjectionView {
            name: Option::Some(name),
            ..self
        }
    }

    pub open spec fn items_field() -> nat {0}

    pub open spec fn name_field() -> nat {1}
}

impl Marshalable for ConfigMapProjectionView {
    open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::items_field(), if self.items.is_None() { Value::Null } else {
                    Value::Array(self.items.get_Some_0().map_values(|x: KeyToPathView| x.marshal()))
                })
                .insert(Self::name_field(), if self.name.is_None() { Value::Null } else {
                    Value::String(self.name.get_Some_0())
                })
        )
    }

    open spec fn unmarshal(value: Value) -> Self {
        ConfigMapProjectionView {
            items: if value.get_Object_0()[Self::items_field()].is_Null() { Option::None } else {
                Option::Some(value.get_Object_0()[Self::items_field()].get_Array_0().map_values(|x| KeyToPathView::unmarshal(x)))
            },
            name: if value.get_Object_0()[Self::name_field()].is_Null() { Option::None } else {
                Option::Some(value.get_Object_0()[Self::name_field()].get_String_0())
            },
        }
    }

    proof fn marshal_preserves_integrity() {
        assert forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()) by {
            if o.items.is_Some() {
                assert_seqs_equal!(o.items.get_Some_0(), Self::unmarshal(o.marshal()).items.get_Some_0());
            }
        }
    }
}





pub struct SecretProjectionView {
    pub items: Option<Seq<KeyToPathView>>,
    pub name: Option<StringView>
}

impl SecretProjectionView {
    pub open spec fn default() -> SecretProjectionView {
        SecretProjectionView {
            items: Option::None,
            name: Option::None,
        }
    }

    pub open spec fn set_items(self, items: Seq<KeyToPathView>) -> SecretProjectionView {
        SecretProjectionView {
            items: Option::Some(items),
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> SecretProjectionView {
        SecretProjectionView {
            name: Option::Some(name),
            ..self
        }
    }

    pub open spec fn items_field() -> nat {0}

    pub open spec fn name_field() -> nat {1}
}

impl Marshalable for SecretProjectionView {
    open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::items_field(), if self.items.is_None() { Value::Null } else {
                    Value::Array(self.items.get_Some_0().map_values(|x: KeyToPathView| x.marshal()))
                })
                .insert(Self::name_field(), if self.name.is_None() { Value::Null } else {
                    Value::String(self.name.get_Some_0())
                })
        )
    }

    open spec fn unmarshal(value: Value) -> Self {
        SecretProjectionView {
            items: if value.get_Object_0()[Self::items_field()].is_Null() { Option::None } else {
                Option::Some(value.get_Object_0()[Self::items_field()].get_Array_0().map_values(|x| KeyToPathView::unmarshal(x)))
            },
            name: if value.get_Object_0()[Self::name_field()].is_Null() { Option::None } else {
                Option::Some(value.get_Object_0()[Self::name_field()].get_String_0())
            },
        }
    }

    proof fn marshal_preserves_integrity() {
        assert forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()) by {
            if o.items.is_Some() {
                assert_seqs_equal!(o.items.get_Some_0(), Self::unmarshal(o.marshal()).items.get_Some_0());
            }
        }
    }
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

    pub open spec fn key_field() -> nat {0}

    pub open spec fn path_field() -> nat {1}
}

impl Marshalable for KeyToPathView {
    open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::key_field(), Value::String(self.key))
                .insert(Self::path_field(), Value::String(self.path))
        )
    }

    open spec fn unmarshal(value: Value) -> Self {
        KeyToPathView {
            key: value.get_Object_0()[Self::key_field()].get_String_0(),
            path: value.get_Object_0()[Self::path_field()].get_String_0(),
        }
    }

    proof fn marshal_preserves_integrity() {}
}

pub struct DownwardAPIVolumeSourceView {
    pub items: Option<Seq<DownwardAPIVolumeFileView>>,
}
impl DownwardAPIVolumeSourceView {
    pub open spec fn default() -> DownwardAPIVolumeSourceView {
        DownwardAPIVolumeSourceView {
            items: Option::None,
        }
    }

    pub open spec fn set_items(self, items: Seq<DownwardAPIVolumeFileView>) -> DownwardAPIVolumeSourceView {
        DownwardAPIVolumeSourceView {
            items: Option::Some(items),
            ..self
        }
    }

    pub open spec fn items_field() -> nat {0}
}

impl Marshalable for DownwardAPIVolumeSourceView {
    open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::items_field(), if self.items.is_None() { Value::Null } else {
                    Value::Array(self.items.get_Some_0().map_values(|x: DownwardAPIVolumeFileView| x.marshal()))
                })
        )
    }

    open spec fn unmarshal(value: Value) -> Self {
        DownwardAPIVolumeSourceView {
            items: if value.get_Object_0()[Self::items_field()].is_Null() { Option::None } else {
                Option::Some(value.get_Object_0()[Self::items_field()].get_Array_0().map_values(|x| DownwardAPIVolumeFileView::unmarshal(x)))
            },
        }
    }

    proof fn marshal_preserves_integrity() {
        assert forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()) by {
            if o.items.is_Some() {
                assert_seqs_equal!(o.items.get_Some_0(), Self::unmarshal(o.marshal()).items.get_Some_0());
            }
        }
    }
}

pub struct DownwardAPIVolumeFileView {
    pub field_ref: Option<ObjectFieldSelectorView>,
    pub path: StringView,
}
impl DownwardAPIVolumeFileView {
    pub open spec fn default() -> DownwardAPIVolumeFileView {
        DownwardAPIVolumeFileView {
            field_ref: Option::None,
            path: new_strlit("")@,
        }
    }

    pub open spec fn set_field_ref(self, field_ref: ObjectFieldSelectorView) -> DownwardAPIVolumeFileView {
        DownwardAPIVolumeFileView {
            field_ref: Option::Some(field_ref),
            ..self
        }
    }

    pub open spec fn set_path(self, path: StringView) -> DownwardAPIVolumeFileView {
        DownwardAPIVolumeFileView {
            path,
            ..self
        }
    }

    pub open spec fn field_ref_field() -> nat {0}

    pub open spec fn path_field() -> nat {1}
}

impl Marshalable for DownwardAPIVolumeFileView {
    open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::field_ref_field(), if self.field_ref.is_None() { Value::Null } else {
                    self.field_ref.get_Some_0().marshal()
                })
                .insert(Self::path_field(), Value::String(self.path))
        )
    }

    open spec fn unmarshal(value: Value) -> Self {
        DownwardAPIVolumeFileView {
            field_ref: if value.get_Object_0()[Self::field_ref_field()].is_Null() { Option::None } else {
                Option::Some(ObjectFieldSelectorView::unmarshal(value.get_Object_0()[Self::field_ref_field()]))
            },
            path: value.get_Object_0()[Self::path_field()].get_String_0(),
        }
    }

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

    pub open spec fn field_path_field() -> nat {0}
}
impl Marshalable for ObjectFieldSelectorView {
    open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::field_path_field(), Value::String(self.field_path))
        )
    }

    open spec fn unmarshal(value: Value) -> Self {
        ObjectFieldSelectorView {
            field_path: value.get_Object_0()[Self::field_path_field()].get_String_0(),
        }
    }

    proof fn marshal_preserves_integrity() {}
}


}
