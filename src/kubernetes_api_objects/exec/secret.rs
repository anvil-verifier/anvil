// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, object_meta::*, resource::*,
};
use crate::kubernetes_api_objects::spec::{resource::*, secret::*};
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;

// Secret is a type of API object used to store confidential data in key-value pairs.
// A Secret object can be used to set environment variables or configuration files
// in a Volume mounted to a Pod.
//
// This definition is a wrapper of Secret defined at
// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/secret.rs.
// It is supposed to be used in exec controller code.
//
// More detailed information: https://kubernetes.io/docs/concepts/configuration/secret/.

implement_wrapper_type!(
    Secret,
    deps_hack::k8s_openapi::api::core::v1::Secret,
    SecretView
);

verus! {

impl Secret {
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

    // TODO: data is a map of string to bytestring. May support it in the future.
    #[verifier(external_body)]
    pub fn set_data(&mut self, data: StringMap)
        ensures self@ == old(self)@.with_data(data@),
    {
        let string_map = data.into_rust_map();
        let mut binary_map = std::collections::BTreeMap::new();
        for (key, value) in string_map {
            binary_map.insert(key, deps_hack::k8s_openapi::ByteString(value.into_bytes()));
        }
        self.inner.data = Some(binary_map)
    }
}

}
