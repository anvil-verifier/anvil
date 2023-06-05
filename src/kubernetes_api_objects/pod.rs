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

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Volume {
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
        self.inner.name = std::option::Option::Some(name.into_rust_string());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ConfigMapVolumeSource {
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
}

impl PodSpecView {
    pub open spec fn default() -> PodSpecView {
        PodSpecView {
            containers: Seq::empty(),
            volumes: Option::None,
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
}

impl VolumeMountView {
    pub open spec fn default() -> VolumeMountView {
        VolumeMountView {
            mount_path: new_strlit("")@,
            name: new_strlit("")@,
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
}

impl VolumeView {
    pub open spec fn default() -> VolumeView {
        VolumeView {
            name: new_strlit("")@,
            config_map: Option::Some(ConfigMapVolumeSourceView::default()),
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

}
