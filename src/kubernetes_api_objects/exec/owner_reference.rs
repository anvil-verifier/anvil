// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::spec::owner_reference::*;
use vstd::prelude::*;

verus! {


// OwnerReference contains enough information to let you identify an owning object.
// An owning object must be in the same namespace as the dependent, or be cluster-scoped, so there is no namespace field.
//
// This definition is a wrapper of OwnerReference defined at
// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/apimachinery/pkg/apis/meta/v1/owner_reference.rs.
// It is supposed to be used in exec controller code.
//

#[verifier(external_body)]
pub struct OwnerReference {
    inner: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference,
}

impl OwnerReference {
    pub uninterp spec fn view(&self) -> OwnerReferenceView;

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures s@ == self@,
    {
        OwnerReference { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn controller(&self) -> (controller: Option<bool>)
        ensures
            self@.controller is Some == controller is Some,
            controller is Some ==> controller->0 == self@.controller->0,
    {
        match &self.inner.controller {
            Some(c) => Some(*c),
            None => None,
        }
    }

    #[verifier(external)]
    pub fn as_kube_ref(&self) -> &deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference {
        &self.inner
    }

    #[verifier(external)]
    pub fn as_kube_mut_ref(&mut self) -> &mut deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference {
        &mut self.inner
    }
}

}

implement_resource_wrapper_trait!(
    OwnerReference,
    deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference
);
