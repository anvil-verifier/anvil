// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, object_meta::*, resource::*,
};
use crate::kubernetes_api_objects::spec::{config_map::*, resource::*};
use crate::vstd_ext::{string_map::*, string_view::*};
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

impl View for ConfigMap {
    type V = ConfigMapView;

    spec fn view(&self) -> ConfigMapView;
}

impl ConfigMap {
    #[verifier(external_body)]
    pub fn default() -> (config_map: ConfigMap)
        ensures config_map@ == ConfigMapView::default(),
    {
        ConfigMap { inner: deps_hack::k8s_openapi::api::core::v1::ConfigMap::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (c: Self)
        ensures c@ == self@,
    {
        ConfigMap { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
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
        ensures self@ == old(self)@.set_metadata(metadata@),
    {
        self.inner.metadata = metadata.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_data(&mut self, data: StringMap)
        ensures self@ == old(self)@.set_data(data@),
    {
        self.inner.data = Some(data.into_rust_map())
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures res@.kind == ConfigMapView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::core::v1::ConfigMap>(&()))
    }

    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures obj@ == self@.marshal(),
    {
        DynamicObject::from_kube(deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap())
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

#[verifier(external)]
impl ResourceWrapper<deps_hack::k8s_openapi::api::core::v1::ConfigMap> for ConfigMap {
    fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::ConfigMap) -> ConfigMap { ConfigMap { inner: inner } }

    fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ConfigMap { self.inner }
}

}
