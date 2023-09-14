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

/// Quantity is a group of affinity scheduling rules.
///
/// This definition is a wrapper of Quantity defined at
/// https://github.com/Arnavion/k8s-openapi/blob/master/src/v1_26/api/core/v1/affinity.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/scheduling-eviction/assign-pod-node/#affinity-and-anti-affinity.

#[verifier(external_body)]
pub struct Quantity {
    inner: deps_hack::k8s_openapi::apimachinery::pkg::api::resource::Quantity,
}

impl Quantity {
    pub spec fn view(&self) -> QuantityView;

    #[verifier(external_body)]
    pub fn eq(&self, quantity: String) -> (res: bool)
        ensures
            res == self@.eq(quantity@),
    {
        return self.inner.0 == quantity.into_rust_string();
    }
}

impl ResourceWrapper<deps_hack::k8s_openapi::apimachinery::pkg::api::resource::Quantity> for Quantity {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::k8s_openapi::apimachinery::pkg::api::resource::Quantity) -> Quantity {
        Quantity {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::k8s_openapi::apimachinery::pkg::api::resource::Quantity {
        self.inner
    }
}

/// QuantityView is the ghost type of Quantity.
/// It is supposed to be used in spec and proof code.

pub struct QuantityView {
    pub quantity: StringView,
}

impl QuantityView {
    pub open spec fn eq(self, quantity: StringView) -> bool {
        self.quantity == quantity
    }
}

}