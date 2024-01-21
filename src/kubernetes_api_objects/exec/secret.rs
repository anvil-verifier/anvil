// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, object_meta::*, resource::*,
};
use crate::kubernetes_api_objects::spec::{resource::*, secret::*};
use crate::vstd_ext::string_map::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

/// Secret is a type of API object used to store confidential data in key-value pairs.
/// A Secret object can be used to set environment variables or configuration files
/// in a Volume mounted to a Pod.
///
/// This definition is a wrapper of Secret defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/secret.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/configuration/secret/.

#[verifier(external_body)]
pub struct Secret {
    inner: deps_hack::k8s_openapi::api::core::v1::Secret,
}

impl View for Secret {
    type V = SecretView;

    spec fn view(&self) -> SecretView;
}

impl Secret {
    #[verifier(external_body)]
    pub fn default() -> (secret: Secret)
        ensures secret@ == SecretView::default(),
    {
        Secret {
            inner: deps_hack::k8s_openapi::api::core::v1::Secret::default(),
        }
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
            Some(d) => {
                let binary_map = d.clone();
                let mut string_map = std::collections::BTreeMap::new();
                for (key, value) in binary_map {
                    // NOTE: unwrap might panic here if value.0 is invalid utf8 sequence!
                    string_map.insert(key, std::string::String::from_utf8(value.0).unwrap());
                }
                Some(StringMap::from_rust_map(string_map))
            },
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn set_metadata(&mut self, metadata: ObjectMeta)
        ensures self@ == old(self)@.set_metadata(metadata@),
    {
        self.inner.metadata = metadata.into_kube();
    }

    // TODO: data is a map of string to bytestring. May support it in the future.
    #[verifier(external_body)]
    pub fn set_data(&mut self, data: StringMap)
        ensures self@ == old(self)@.set_data(data@),
    {
        let string_map = data.into_rust_map();
        let mut binary_map = std::collections::BTreeMap::new();
        for (key, value) in string_map {
            binary_map.insert(key, deps_hack::k8s_openapi::ByteString(value.into_bytes()));
        }
        self.inner.data = Some(binary_map)
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (c: Self)
        ensures c@ == self@,
    {
        Secret { inner: self.inner.clone() }
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::Secret) -> Secret { Secret { inner: inner } }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Secret { self.inner }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures res@.kind == SecretView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::core::v1::Secret>(&()))
    }

    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures obj@ == self@.marshal(),
    {
        DynamicObject::from_kube(deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap())
    }

    #[verifier(external_body)]
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<Secret, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == SecretView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == SecretView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::core::v1::Secret>();
        if parse_result.is_ok() {
            let res = Secret { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

}
