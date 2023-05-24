// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;
use vstd::vec::*;

verus! {

#[verifier(external_body)]
pub struct Pod {
    inner: k8s_openapi::api::core::v1::Pod,
}

impl Pod {
    pub spec fn view(&self) -> PodView;

    #[verifier(external_body)]
    pub fn default() -> (pod: Pod)
        ensures
            pod@ == PodView::default(),
    {
        Pod {
            inner: k8s_openapi::api::core::v1::Pod::default(),
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
    pub fn into_kube(self) -> k8s_openapi::api::core::v1::Pod {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == Kind::CustomResourceKind,
    {
        ApiResource::from_kube(kube::api::ApiResource::erase::<k8s_openapi::api::core::v1::Pod>(&()))
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        DynamicObject::from_kube(
            k8s_openapi::serde_json::from_str(&k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    /// Convert a DynamicObject to a Pod
    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (pod: Pod)
        ensures
            pod@ == PodView::from_dynamic_object(obj@),
    {
        Pod { inner: obj.into_kube().try_parse::<k8s_openapi::api::core::v1::Pod>().unwrap() }
    }
}

#[verifier(external_body)]
pub struct PodSpec {
    inner: k8s_openapi::api::core::v1::PodSpec,
}

impl PodSpec {
    pub spec fn view(&self) -> PodSpecView;

    #[verifier(external_body)]
    pub fn default() -> (pod_spec: PodSpec)
        ensures
            pod_spec@ == PodSpecView::default(),
    {
        PodSpec {
            inner: k8s_openapi::api::core::v1::PodSpec::default(),
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
    pub fn into_kube(self) -> k8s_openapi::api::core::v1::PodSpec {
        self.inner
    }
}

#[verifier(external_body)]
pub struct Container {
    inner: k8s_openapi::api::core::v1::Container,
}

impl Container {
    pub spec fn view(&self) -> ContainerView;

    #[verifier(external_body)]
    pub fn default() -> (container: Container)
        ensures
            container@ == ContainerView::default(),
    {
        Container {
            inner: k8s_openapi::api::core::v1::Container::default(),
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
    pub fn into_kube(self) -> k8s_openapi::api::core::v1::Container {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ContainerPort {
    inner: k8s_openapi::api::core::v1::ContainerPort,
}

impl ContainerPort {
    pub spec fn view(&self) -> ContainerPortView;

    #[verifier(external_body)]
    pub fn default() -> (container_port: ContainerPort)
        ensures
            container_port@ == ContainerPortView::default(),
    {
        ContainerPort {
            inner: k8s_openapi::api::core::v1::ContainerPort::default(),
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
    pub fn into_kube(self) -> k8s_openapi::api::core::v1::ContainerPort {
        self.inner
    }
}

#[verifier(external_body)]
pub struct Probe {
    inner: k8s_openapi::api::core::v1::Probe,
}

impl Probe {
    #[verifier(external)]
    pub fn from_kube(inner: k8s_openapi::api::core::v1::Probe) -> Probe {
        Probe { inner: inner }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> k8s_openapi::api::core::v1::Probe {
        self.inner
    }
}

#[verifier(external_body)]
pub struct VolumeMount {
    inner: k8s_openapi::api::core::v1::VolumeMount,
}

impl VolumeMount {
    pub spec fn view(&self) -> VolumeMountView;

    #[verifier(external_body)]
    pub fn default() -> (volume_mount: VolumeMount)
        ensures
            volume_mount@ == VolumeMountView::default(),
    {
        VolumeMount {
            inner: k8s_openapi::api::core::v1::VolumeMount::default(),
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
    pub fn into_kube(self) -> k8s_openapi::api::core::v1::VolumeMount {
        self.inner
    }
}

#[verifier(external_body)]
pub struct Volume {
    inner: k8s_openapi::api::core::v1::Volume,
}

impl Volume {
    pub spec fn view(&self) -> VolumeView;

    #[verifier(external_body)]
    pub fn default() -> (volume: Volume)
        ensures
            volume@ == VolumeView::default(),
    {
        Volume {
            inner: k8s_openapi::api::core::v1::Volume::default(),
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
    pub fn into_kube(self) -> k8s_openapi::api::core::v1::Volume {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ConfigMapVolumeSource {
    inner: k8s_openapi::api::core::v1::ConfigMapVolumeSource,
}

impl ConfigMapVolumeSource {
    pub spec fn view(&self) -> ConfigMapVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (config_map_volume_source: ConfigMapVolumeSource)
        ensures
            config_map_volume_source@ == ConfigMapVolumeSourceView::default(),
    {
        ConfigMapVolumeSource {
            inner: k8s_openapi::api::core::v1::ConfigMapVolumeSource::default(),
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
    pub fn into_kube(self) -> k8s_openapi::api::core::v1::ConfigMapVolumeSource {
        self.inner
    }
}

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

    pub open spec fn spec_field() -> nat {0}
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
            data: Value::Object(Map::empty()
                                    .insert(Self::spec_field(), if self.spec.is_None() { Value::Null } else {
                                        self.spec.get_Some_0().marshal()
                                    })),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> PodView {
        PodView {
            metadata: obj.metadata,
            spec: if obj.data.get_Object_0()[Self::spec_field()].is_Null() { Option::None } else {
                Option::Some(PodSpecView::unmarshal(obj.data.get_Object_0()[Self::spec_field()]))
            },
        }
    }

    proof fn integrity_check() {
        PodSpecView::integrity_check();
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

    pub open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::containers_field(), Value::Array(self.containers.map_values(|container: ContainerView| container.marshal())))
                .insert(Self::volumes_field(), if self.volumes.is_None() { Value::Null } else {
                    Value::Array(self.volumes.get_Some_0().map_values(|volume: VolumeView| volume.marshal()))
                })
        )
    }

    pub open spec fn unmarshal(value: Value) -> Self {
        PodSpecView {
            containers: value.get_Object_0()[Self::containers_field()].get_Array_0().map_values(|v| ContainerView::unmarshal(v)),
            volumes: if value.get_Object_0()[Self::volumes_field()].is_Null() { Option::None } else {
                Option::Some(value.get_Object_0()[Self::volumes_field()].get_Array_0().map_values(|v| VolumeView::unmarshal(v)))
            },
        }
    }

    pub proof fn integrity_check()
        ensures forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()),
    {
        assert forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()) by {
            ContainerView::integrity_check();
            assert_seqs_equal!(o.containers, Self::unmarshal(o.marshal()).containers);
            if o.volumes.is_Some() {
                assert_seqs_equal!(o.volumes.get_Some_0(), Self::unmarshal(o.marshal()).volumes.get_Some_0());
            }
        }
    }

    pub open spec fn containers_field() -> nat {0}

    pub open spec fn volumes_field() -> nat {1}
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

    pub open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::image_field(), if self.image.is_None() {Value::Null} else {
                    Value::String(self.image.get_Some_0())
                })
                .insert(Self::name_field(), Value::String(self.name))
                .insert(Self::ports_field(), if self.ports.is_None() {Value::Null} else {
                    Value::Array(self.ports.get_Some_0().map_values(|port: ContainerPortView| port.marshal()))
                })
                .insert(Self::volume_mounts_field(), if self.volume_mounts.is_None() {Value::Null} else {
                    Value::Array(self.volume_mounts.get_Some_0().map_values(|volume_mount: VolumeMountView| volume_mount.marshal()))
                })
        )
    }

    pub open spec fn unmarshal(value: Value) -> Self {
        ContainerView {
            image: if value.get_Object_0()[Self::image_field()].is_Null() {Option::None} else {
                Option::Some(value.get_Object_0()[Self::image_field()].get_String_0())
            },
            name: value.get_Object_0()[Self::name_field()].get_String_0(),
            ports: if value.get_Object_0()[Self::ports_field()].is_Null() {Option::None} else {
                Option::Some(value.get_Object_0()[Self::ports_field()].get_Array_0().map_values(|v| ContainerPortView::unmarshal(v)))
            },
            volume_mounts: if value.get_Object_0()[Self::volume_mounts_field()].is_Null() {Option::None} else {
                Option::Some(value.get_Object_0()[Self::volume_mounts_field()].get_Array_0().map_values(|v| VolumeMountView::unmarshal(v)))
            },
        }
    }

    proof fn integrity_check()
        ensures forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()),
    {
        assert forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()) by {
            if o.ports.is_Some() {
                assert_seqs_equal!(o.ports.get_Some_0(), Self::unmarshal(o.marshal()).ports.get_Some_0());
            }
            if o.volume_mounts.is_Some() {
                assert_seqs_equal!(o.volume_mounts.get_Some_0(), Self::unmarshal(o.marshal()).volume_mounts.get_Some_0());
            }
        }
    }

    pub open spec fn image_field() -> nat {0}

    pub open spec fn name_field() -> nat {1}

    pub open spec fn ports_field() -> nat {2}

    pub open spec fn volume_mounts_field() -> nat {3}
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

    pub open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::container_port_field(), Value::Int(self.container_port))
                .insert(Self::name_field(), if self.name.is_None() {Value::Null} else {
                    Value::String(self.name.get_Some_0())
                })
        )
    }

    pub open spec fn unmarshal(value: Value) -> Self {
        ContainerPortView {
            container_port: value.get_Object_0()[Self::container_port_field()].get_Int_0(),
            name: if value.get_Object_0()[Self::name_field()].is_Null() {Option::None} else {
                Option::Some(value.get_Object_0()[Self::name_field()].get_String_0())
            },
        }
    }

    proof fn integrity_check()
        ensures forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal())
    {}

    pub open spec fn container_port_field() -> nat {0}

    pub open spec fn name_field() -> nat {1}
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

    pub open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::mount_path_field(), Value::String(self.mount_path))
                .insert(Self::name_field(), Value::String(self.name))
        )
    }

    pub open spec fn unmarshal(value: Value) -> Self {
        VolumeMountView {
            mount_path: value.get_Object_0()[Self::mount_path_field()].get_String_0(),
            name: value.get_Object_0()[Self::name_field()].get_String_0(),
        }
    }

    proof fn integrity_check()
        ensures forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal())
    {}

    pub open spec fn mount_path_field() -> nat {0}

    pub open spec fn name_field() -> nat {1}
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

    pub open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::config_map_field(), if self.config_map.is_None() {Value::Null} else {
                    self.config_map.get_Some_0().marshal()
                })
                .insert(Self::name_field(), Value::String(self.name))
        )
    }

    pub open spec fn unmarshal(value: Value) -> Self {
        VolumeView {
            config_map: if value.get_Object_0()[Self::config_map_field()].is_Null() {Option::None} else {
                Option::Some(ConfigMapVolumeSourceView::unmarshal(value.get_Object_0()[Self::config_map_field()]))
            },
            name: value.get_Object_0()[Self::name_field()].get_String_0(),
        }
    }

    proof fn integrity_check()
        ensures forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()),
    {}

    pub open spec fn config_map_field() -> nat {0}

    pub open spec fn name_field() -> nat {1}
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

    pub open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::name_field(), if self.name.is_None() { Value::Null } else {
                    Value::String(self.name.get_Some_0())
                })
        )
    }

    pub open spec fn unmarshal(value: Value) -> Self {
        ConfigMapVolumeSourceView {
            name: if value.get_Object_0()[Self::name_field()].is_Null() { Option::None } else {
                Option::Some(value.get_Object_0()[Self::name_field()].get_String_0())
            },
        }
    }

    proof fn integrity_check()
        ensures forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()),
    {}

    pub open spec fn name_field() -> nat {0}
}


}
