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

/// The pod this Toleration is attached to tolerates any taint that matches
///
/// This definition is a wrapper of Toleration defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/toleration.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/scheduling-eviction/taint-and-toleration/.

#[verifier(external_body)]
pub struct Toleration {
    inner: deps_hack::k8s_openapi::api::core::v1::Toleration,
}

impl Toleration {
    pub spec fn view(&self) -> TolerationView;
}

impl ResourceWrapper<deps_hack::k8s_openapi::api::core::v1::Toleration> for Toleration {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::Toleration) -> Toleration {
        Toleration {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Toleration {
        self.inner
    }
}

/// TolerationView is the ghost type of Toleration.
/// It is supposed to be used in spec and proof code.

pub struct TolerationView {}

impl TolerationView {}

}
