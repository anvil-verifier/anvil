// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, object_meta::*, resource::*,
};
use crate::kubernetes_api_objects::spec::{config_map::*, resource::*};
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;

// ConfigMap is a type of API object used to store non-confidential data in key-value pairs.
// A ConfigMap object can be used to set environment variables or configuration files
// in a Volume mounted to a Pod.
//
// This definition is a wrapper of ConfigMap defined at
// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/config_map.rs.
// It is supposed to be used in exec controller code.
//
// More detailed information: https://kubernetes.io/docs/concepts/configuration/configmap/.

implement_object_wrapper_type!(
    ConfigMap,
    deps_hack::k8s_openapi::api::core::v1::ConfigMap,
    ConfigMapView
);

verus! {

impl ConfigMap {
    #[verifier(external_body)]
    pub fn data(&self) -> (data: Option<StringMap>)
        ensures
            self@.data is Some == data is Some,
            data is Some ==> data->0@ == self@.data->0,
    {
        match &self.inner.data {
            Some(d) => Some(StringMap::from_rust_map(d.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn set_data(&mut self, data: StringMap)
        ensures self@ == old(self)@.with_data(data@),
    {
        self.inner.data = Some(data.into_rust_map())
    }
}

}

implement_resource_wrapper_trait!(ConfigMap, deps_hack::k8s_openapi::api::core::v1::ConfigMap);
