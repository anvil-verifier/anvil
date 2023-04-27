// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::object_meta::*;
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
    pub fn into_kube_obj(self) -> K8SConfigMap {
        self.inner
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
            self@.data.is_Some(),
            data@ == self@.data.get_Some_0(),
    {
        todo!()
    }
}

impl ConfigMapView {
    pub open spec fn default() -> ConfigMapView {
        ConfigMapView {
            metadata: ObjectMetaView::default(),
            data: Option::None,
        }
    }

    pub open spec fn kind(self) -> Kind {
        Kind::ConfigMapKind
    }

    pub open spec fn object_ref(self) -> ObjectRef
        recommends
            self.metadata.name.is_Some(),
            self.metadata.namespace.is_Some(),
    {
        ObjectRef {
            kind: self.kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
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

}
