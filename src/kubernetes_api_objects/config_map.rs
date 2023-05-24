// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct ConfigMap {
    inner: k8s_openapi::api::core::v1::ConfigMap,
}

impl ConfigMap {
    pub spec fn view(&self) -> ConfigMapView;

    #[verifier(external_body)]
    pub fn default() -> (config_map: ConfigMap)
        ensures
            config_map@ == ConfigMapView::default(),
    {
        ConfigMap {
            inner: k8s_openapi::api::core::v1::ConfigMap::default(),
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
    pub fn data(&self) -> (data: Option<StringMap>)
        ensures
            self@.data.is_Some() == data.is_Some(),
            data.is_Some() ==> data.get_Some_0()@ == self@.data.get_Some_0(),
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
    pub fn set_data(&mut self, data: StringMap)
        ensures
            self@ == old(self)@.set_data(data@),
    {
        self.inner.data = std::option::Option::Some(data.into_rust_map())
    }

    #[verifier(external)]
    pub fn from_kube(inner: k8s_openapi::api::core::v1::ConfigMap) -> ConfigMap {
        ConfigMap {
            inner: inner
        }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> k8s_openapi::api::core::v1::ConfigMap {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == Kind::ConfigMapKind,
    {
        ApiResource::from_kube(kube::api::ApiResource::erase::<k8s_openapi::api::core::v1::ConfigMap>(&()))
    }

    #[verifier(external_body)]
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        DynamicObject::from_kube(
            k8s_openapi::serde_json::from_str(&k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (cm: ConfigMap)
        ensures
            cm@ == ConfigMapView::from_dynamic_object(obj@),
    {
        ConfigMap {inner: obj.into_kube().try_parse::<k8s_openapi::api::core::v1::ConfigMap>().unwrap()}
    }
}

pub struct ConfigMapView {
    pub metadata: ObjectMetaView,
    pub data: Option<Map<StringView, StringView>>,
}

impl ConfigMapView {
    pub open spec fn default() -> ConfigMapView {
        ConfigMapView {
            metadata: ObjectMetaView::default(),
            data: Option::None,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> ConfigMapView {
        ConfigMapView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_data(self, data: Map<StringView, StringView>) -> ConfigMapView {
        ConfigMapView {
            data: Option::Some(data),
            ..self
        }
    }

    pub open spec fn data_field() -> nat {0}
}

impl ResourceView for ConfigMapView {
    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind(self) -> Kind {
        Kind::ConfigMapKind
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
            data: Value::Object(
                Map::empty()
                .insert(Self::data_field(),
                        if self.data.is_None() { Value::Null } else {
                            Value::StringStringMap(self.data.get_Some_0())
                        }
                )
            ),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> ConfigMapView {
        ConfigMapView {
            metadata: obj.metadata,
            data: if obj.data.get_Object_0()[Self::data_field()].is_Null() { Option::None } else {
                Option::Some(obj.data.get_Object_0()[Self::data_field()].get_StringStringMap_0())
            },
        }
    }

    proof fn to_dynamic_preserves_integrity() {}
}

}
