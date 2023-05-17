// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

use k8s_openapi::api::core::v1::ConfigMap as K8SConfigMap;
use k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta as K8SObjectMeta;

verus! {

#[verifier(external_body)]
pub struct ConfigMap {
    inner: K8SConfigMap,
}

pub struct ConfigMapView {
    pub metadata: ObjectMetaView,
    pub data: Option<Map<StringView, StringView>>,
}

impl ConfigMap {
    pub spec fn view(&self) -> ConfigMapView;

    #[verifier(external_body)]
    pub fn default() -> (config_map: ConfigMap)
        ensures
            config_map@ == ConfigMapView::default(),
    {
        ConfigMap {
            inner: K8SConfigMap::default(),
        }
    }

    #[verifier(external)]
    pub fn from_kube_obj(inner: K8SConfigMap) -> ConfigMap {
        ConfigMap {
            inner: inner
        }
    }

    #[verifier(external)]
    pub fn into_kube_obj(self) -> K8SConfigMap {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == Kind::ConfigMapKind,
    {
        ApiResource::from_kube_api_resource(kube::api::ApiResource::erase::<K8SConfigMap>(&()))
    }

    /// Convert a ConfigMap to a DynamicObject
    // NOTE: This function assumes serde_json::to_value won't fail!
    #[verifier(external_body)]
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        DynamicObject::from_kube_obj(kube::api::DynamicObject {
            types: std::option::Option::Some(kube::api::TypeMeta {
                api_version: Self::api_resource().into_kube_api_resource().api_version,
                kind: Self::api_resource().into_kube_api_resource().kind,
            }),
            metadata: self.inner.metadata,
            data: k8s_openapi::serde_json::to_value(self.inner.data).unwrap(),
        })
    }

    /// Convert a DynamicObject to a ConfigMap
    // NOTE: This function assumes try_parse won't fail!
    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (cm: ConfigMap)
        ensures
            cm@ == ConfigMapView::from_dynamic_object(obj@),
    {
        ConfigMap {inner: obj.into_kube_obj().try_parse::<K8SConfigMap>().unwrap()}
    }

    #[verifier(external)]
    pub fn kube_metadata_ref(&self) -> &K8SObjectMeta {
        &self.inner.metadata
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.metadata.name = std::option::Option::Some(name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_namespace(&mut self, namespace: String)
        ensures
            self@ == old(self)@.set_namespace(namespace@),
    {
        self.inner.metadata.namespace = std::option::Option::Some(namespace.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn data(&self) -> (data: Option<string_map::StringMap>)
        ensures
            self@.data.is_Some() == data.is_Some(),
            data.is_Some() ==> data.get_Some_0()@ == self@.data.get_Some_0(),
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn set_data(&mut self, data: string_map::StringMap)
        ensures
            self@ == old(self)@.set_data(data@),
            // self@.data.is_Some(),
            // data@ == self@.data.get_Some_0(),
    {
        self.inner.data = std::option::Option::Some(data.inner);
    }
}

impl ConfigMapView {
    pub open spec fn default() -> ConfigMapView {
        ConfigMapView {
            metadata: ObjectMetaView::default(),
            data: Option::None,
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ConfigMapView {
        ConfigMapView {
            metadata: self.metadata.set_name(name),
            ..self
        }
    }

    pub open spec fn set_namespace(self, namespace: StringView) -> ConfigMapView {
        ConfigMapView {
            metadata: self.metadata.set_namespace(namespace),
            ..self
        }
    }
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

    // TODO: defining spec functions like data_field() to serve as the key of Object Map
    // is not the ideal way. Find a more elegant way to define the keys.
    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: self.kind(),
            metadata: self.metadata,
            data: Value::Object(
                Map::empty()
                .insert(data_field(),
                        if self.data.is_None() {
                            Value::Null
                        } else {
                            Value::StringStringMap(self.data.get_Some_0())
                        }
                )
            ),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> ConfigMapView {
        ConfigMapView {
            metadata: obj.metadata,
            data: if obj.data.get_Object_0()[data_field()].is_Null() {
                Option::None
            } else {
                Option::Some(obj.data.get_Object_0()[data_field()].get_StringStringMap_0())
            },
        }
    }

    /// Check that any config map remains unchanged after serialization and deserialization
    proof fn integrity_check() {}
    pub open spec fn set_data(self, data: Map<StringView, StringView>) -> ConfigMapView {
        ConfigMapView {
            data: Option::Some(data),
            ..self
        }
    }
}


pub open spec fn data_field() -> nat {0}

}
