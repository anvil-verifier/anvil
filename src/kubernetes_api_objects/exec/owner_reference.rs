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

implement_field_wrapper_type!(
    OwnerReference,
    deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference,
    OwnerReferenceView
);

impl OwnerReference {
    #[verifier(external_body)]
    pub fn controller(&self) -> (controller: Option<bool>)
        ensures self@.controller == controller.deep_view()
    {
        match &self.inner.controller {
            Some(c) => Some(*c),
            None => None,
        }
    }
}

}

implement_resource_wrapper_trait!(
    OwnerReference,
    deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference
);
