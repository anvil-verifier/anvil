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

/// Affinity is a group of affinity scheduling rules.
///
/// This definition is a wrapper of Affinity defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/affinity.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/scheduling-eviction/assign-pod-node/#affinity-and-anti-affinity.

#[verifier(external_body)]
pub struct Affinity {
    inner: deps_hack::k8s_openapi::api::core::v1::Affinity,
}

impl Affinity {
    pub spec fn view(&self) -> AffinityView;
}

impl ResourceWrapper<deps_hack::k8s_openapi::api::core::v1::Affinity> for Affinity {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::Affinity) -> Affinity {
        Affinity {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Affinity {
        self.inner
    }
}

/// AffinityView is the ghost type of Affinity.
/// It is supposed to be used in spec and proof code.

pub struct AffinityView {}

impl AffinityView {}

}
