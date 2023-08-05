// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

verus! {

/// ConfigMap is a type of API object used to store non-confidential data in key-value pairs.
/// A ConfigMap object can be used to set environment variables or configuration files
/// in a Volume mounted to a Pod.
///
/// This definition is a wrapper of ConfigMap defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/config_map.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/configuration/configmap/.

#[verifier(external_body)]
pub struct ConfigMap {
    inner: deps_hack::k8s_openapi::api::core::v1::ConfigMap,
}

impl ConfigMap {
    pub spec fn view(&self) -> ConfigMapView;

    #[verifier(external_body)]
    pub fn default() -> (config_map: ConfigMap)
        ensures
            config_map@ == ConfigMapView::default(),
    {
        ConfigMap {
            inner: deps_hack::k8s_openapi::api::core::v1::ConfigMap::default(),
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
    pub fn data(&self) -> (data: Option<StringMap>)
        ensures
            self@.data.is_Some() == data.is_Some(),
            data.is_Some() ==> data.get_Some_0()@ == self@.data.get_Some_0(),
    {
        if self.inner.data.is_none() {
            Option::None
        } else {
            Option::Some(StringMap::from_rust_map(self.inner.data.clone().unwrap()))
        }
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

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == ConfigMapView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::core::v1::ConfigMap>(&()))
    }

    #[verifier(external_body)]
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (res: Result<ConfigMap, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == ConfigMapView::from_dynamic_object(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == ConfigMapView::from_dynamic_object(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::core::v1::ConfigMap>();
        if parse_result.is_ok() {
            let res = ConfigMap { inner: parse_result.unwrap() };
            Result::Ok(res)
        } else {
            Result::Err(ParseDynamicObjectError::ExecError)
        }
    }
}

impl ResourceWrapper<deps_hack::k8s_openapi::api::core::v1::ConfigMap> for ConfigMap {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::ConfigMap) -> ConfigMap {
        ConfigMap {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ConfigMap {
        self.inner
    }
}

/// ConfigMapView is the ghost type of ConfigMap.
/// It is supposed to be used in spec and proof code.

pub struct ConfigMapView {
    pub metadata: ObjectMetaView,
    pub data: Option<Map<StringView, StringView>>,
}

/// This ConfigMapSpecView is defined only to call marshal_spec and unmarshal_spec conveniently
/// Unlike most other Kubernetes objects, a ConfigMap does not have a spec field,
/// but its data, binary_data and immutable fields are treated similarly as spec of other objects.
/// Here we use a tuple to wrap around ConfigMap's fields (we will implement more fields like binary_data later)
/// instead of defining another struct.
///
/// We use a unit type in the tuple because there has to be at least two members in a tuple.
/// The unit type will be replaced once we support other fields than data.
type ConfigMapSpecView = (Option<Map<StringView, StringView>>, ());

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
}

impl ResourceView for ConfigMapView {
    type Spec = ConfigMapSpecView;

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::ConfigMapKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> ConfigMapSpecView {
        (self.data, ())
    }

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: ConfigMapView::marshal_spec((self.data, ())),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<ConfigMapView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else if !ConfigMapView::unmarshal_spec(obj.spec).is_Ok() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Result::Ok(ConfigMapView {
                metadata: obj.metadata,
                data: ConfigMapView::unmarshal_spec(obj.spec).get_Ok_0().0,
            })
        }
    }

    proof fn to_dynamic_preserves_integrity() {
        ConfigMapView::spec_integrity_is_preserved_by_marshal();
    }

    proof fn from_dynamic_preserves_metadata() {}

    proof fn from_dynamic_preserves_kind() {}

    closed spec fn marshal_spec(s: ConfigMapSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<ConfigMapSpecView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn spec_integrity_is_preserved_by_marshal() {}

    open spec fn rule(spec: ConfigMapSpecView) -> bool {
        true
    }

    open spec fn transition_rule(new_spec: ConfigMapSpecView, old_spec: ConfigMapSpecView) -> bool {
        true
    }
}

}
