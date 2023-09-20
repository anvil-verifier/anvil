// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, error::ParseDynamicObjectError, marshal::*,
    object_meta::*, resource::*,
};
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
        ConfigMap { inner: deps_hack::k8s_openapi::api::core::v1::ConfigMap::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (c: Self)
        ensures
            c@ == self@,
    {
        ConfigMap { inner: self.inner.clone() }
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
        match &self.inner.data {
            Some(d) => Some(StringMap::from_rust_map(d.clone())),
            None => None,
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
        self.inner.data = Some(data.into_rust_map())
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == ConfigMapView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::core::v1::ConfigMap>(&()))
    }

    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.marshal(),
    {
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<ConfigMap, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == ConfigMapView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == ConfigMapView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::core::v1::ConfigMap>();
        if parse_result.is_ok() {
            let res = ConfigMap { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
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
            data: None,
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
            data: Some(data),
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

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: ConfigMapView::marshal_spec((self.data, ())),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<ConfigMapView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !ConfigMapView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(ConfigMapView {
                metadata: obj.metadata,
                data: ConfigMapView::unmarshal_spec(obj.spec).get_Ok_0().0,
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        ConfigMapView::marshal_spec_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: ConfigMapSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<ConfigMapSpecView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec() {}

    open spec fn state_validation(self) -> bool {
        true
    }

    open spec fn transition_validation(self, old_obj: ConfigMapView) -> bool {
        true
    }
}

}
