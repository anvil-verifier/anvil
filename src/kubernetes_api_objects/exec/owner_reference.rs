// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::spec::{common::*, owner_reference::*};
use vstd::prelude::*;

verus! {

// OwnerReference contains enough information to let you identify an owning object.
// An owning object must be in the same namespace as the dependent, or be cluster-scoped, so there is no namespace field.
//
// This definition is a wrapper of OwnerReference defined at
// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/apimachinery/pkg/apis/meta/v1/owner_reference.rs.
// It is supposed to be used in exec controller code.
//
// Unlike the other wrappers, OwnerReference is not external_body: all fields of the k8s-openapi
// struct are strings and optional booleans, so its view is defined on them, and the code that
// builds an owner reference (the controllers' controller_owner_ref) is verified against it.

#[verifier::external_type_specification]
#[allow(dead_code)]
pub struct ExK8sOwnerReference(k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference);

pub struct OwnerReference {
    inner: k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference,
}

impl View for OwnerReference {
    type V = OwnerReferenceView;

    closed spec fn view(&self) -> OwnerReferenceView {
        OwnerReferenceView {
            block_owner_deletion: self.inner.block_owner_deletion,
            controller: self.inner.controller,
            kind: owner_reference_kind_view(self.inner.api_version@, self.inner.kind@),
            name: self.inner.name@,
            uid: uid_view(self.inner.uid@),
        }
    }
}

impl std::clone::Clone for OwnerReference {
    fn clone(&self) -> (res: OwnerReference)
        ensures res@ == self@
    {
        OwnerReference {
            inner: k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference {
                api_version: self.inner.api_version.clone(),
                block_owner_deletion: self.inner.block_owner_deletion,
                controller: self.inner.controller,
                kind: self.inner.kind.clone(),
                name: self.inner.name.clone(),
                uid: self.inner.uid.clone(),
            },
        }
    }
}

impl OwnerReference {
    pub fn controller(&self) -> (controller: Option<bool>)
        ensures self@.controller == controller.deep_view()
    {
        self.inner.controller
    }

    // The controller owner reference (controller: Some(true)) to the object with the given
    // apiVersion, kind, name and uid.
    pub fn new_controller_owner_ref(
        api_version: String,
        kind: String,
        name: String,
        uid: String,
        block_owner_deletion: Option<bool>,
    ) -> (owner_reference: OwnerReference)
        ensures
            owner_reference@ == (OwnerReferenceView {
                block_owner_deletion: block_owner_deletion,
                controller: Some(true),
                kind: owner_reference_kind_view(api_version@, kind@),
                name: name@,
                uid: uid_view(uid@),
            }),
    {
        OwnerReference {
            inner: k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference {
                api_version: api_version,
                block_owner_deletion: block_owner_deletion,
                controller: Some(true),
                kind: kind,
                name: name,
                uid: uid,
            },
        }
    }
}

}

implement_deep_view_trait!(OwnerReference, OwnerReferenceView);
implement_default_trait!(
    OwnerReference,
    k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference,
    OwnerReferenceView
);
implement_resource_wrapper_trait!(
    OwnerReference,
    k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference
);
