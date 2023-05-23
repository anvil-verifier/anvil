// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

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
        self.inner.metadata = metadata.into_kube_object_meta();
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: PodSpec)
        ensures
            self@ == old(self)@.set_spec(spec@),
    {
        self.inner.spec = std::option::Option::Some(spec.into_kube_pod_spec());
    }

    #[verifier(external)]
    pub fn into_kube_obj(self) -> k8s_openapi::api::core::v1::Pod {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == Kind::CustomResourceKind,
    {
        ApiResource::from_kube_api_resource(kube::api::ApiResource::erase::<k8s_openapi::api::core::v1::Pod>(&()))
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        DynamicObject::from_kube_obj(
            k8s_openapi::serde_json::from_str(&k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    /// Convert a DynamicObject to a Pod
    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (pod: Pod)
        ensures
            pod@ == PodView::from_dynamic_object(obj@),
    {
        Pod { inner: obj.into_kube_obj().try_parse::<k8s_openapi::api::core::v1::Pod>().unwrap() }
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

    #[verifier(external)]
    pub fn into_kube_pod_spec(self) -> k8s_openapi::api::core::v1::PodSpec {
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
                                    .insert(Self::spec_field(), if self.spec.is_None() {Value::Null} else {
                                        self.spec.get_Some_0().marshal()
                                    })),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> PodView {
        PodView {
            metadata: obj.metadata,
            spec: if obj.data.get_Object_0()[Self::spec_field()].is_Null() {Option::None} else {
                Option::Some(PodSpecView::unmarshal(obj.data.get_Object_0()[Self::spec_field()]))
            },
        }
    }

    proof fn integrity_check() {
        assert forall |o: Self| o == Self::from_dynamic_object(#[trigger] o.to_dynamic_object()) by {
            if o.spec.is_Some() {
                assert_seqs_equal!(
                    o.spec.get_Some_0().containers,
                    Self::from_dynamic_object(o.to_dynamic_object()).spec.get_Some_0().containers
                );
            }
        }
    }
}

pub struct PodSpecView {
    pub containers: Seq<ContainerView>,
}

impl PodSpecView {
    pub open spec fn default() -> PodSpecView {
        PodSpecView {
            containers: Seq::empty(),
        }
    }

    pub open spec fn set_containers(self, containers: Seq<ContainerView>) -> PodSpecView {
        PodSpecView {
            containers: containers,
            ..self
        }
    }

    pub open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::containers_field(), Value::Array(self.containers.map_values(|container: ContainerView| container.marshal())))
        )
    }

    pub open spec fn unmarshal(value: Value) -> Self {
        PodSpecView {
            containers: value.get_Object_0()[Self::containers_field()].get_Array_0().map_values(|v| ContainerView::unmarshal(v)),
        }
    }

    proof fn integrity_check()
        ensures forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()),
    {
        assert forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()) by {
            assert_seqs_equal!(o.containers, Self::unmarshal(o.marshal()).containers);
        }
    }

    pub open spec fn containers_field() -> nat {0}
}

pub struct ContainerView {
    pub image: Option<StringView>,
    pub name: StringView,
}

impl ContainerView {
    pub open spec fn default() -> ContainerView {
        ContainerView {
            image: Option::None,
            name: new_strlit("")@,
        }
    }

    pub open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::image_field(), if self.image.is_None() {Value::Null} else {
                    Value::String(self.image.get_Some_0())
                })
                .insert(Self::name_field(), Value::String(self.name))
        )
    }

    pub open spec fn unmarshal(value: Value) -> Self {
        ContainerView {
            image: if value.get_Object_0()[Self::image_field()].is_Null() {Option::None} else {
                Option::Some(value.get_Object_0()[Self::image_field()].get_String_0())
            },
            name: value.get_Object_0()[Self::name_field()].get_String_0(),
        }
    }

    proof fn integrity_check()
        ensures forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()),
    {}

    pub open spec fn image_field() -> nat {0}

    pub open spec fn name_field() -> nat {1}
}

}
