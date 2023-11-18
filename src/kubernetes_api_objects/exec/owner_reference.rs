// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{common::*, resource::*};
use crate::kubernetes_api_objects::spec::owner_reference::*;
use crate::vstd_ext::{string_map::*, string_view::*};
use vstd::{prelude::*, string::*};

verus! {


/// OwnerReference contains enough information to let you identify an owning object.
/// An owning object must be in the same namespace as the dependent, or be cluster-scoped, so there is no namespace field.
///
/// This definition is a wrapper of OwnerReference defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/apimachinery/pkg/apis/meta/v1/owner_reference.rs.
/// It is supposed to be used in exec controller code.
///

#[verifier(external_body)]
pub struct OwnerReference {
    inner: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference,
}

impl OwnerReference {
    pub spec fn view(&self) -> OwnerReferenceView;
}

impl ResourceWrapper<deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference> for OwnerReference {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference) -> OwnerReference {
        OwnerReference { inner: inner }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference {
        self.inner
    }
}

}
