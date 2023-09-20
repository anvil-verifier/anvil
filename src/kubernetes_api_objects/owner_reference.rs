// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    common::*, error::ParseDynamicObjectError, marshal::*, resource::*,
};
use crate::pervasive_ext::string_map::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

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

/// OwnerReferenceView is the ghost type of OwnerReference.
/// It is supposed to be used in spec and proof code.

pub struct OwnerReferenceView {
    pub block_owner_deletion: Option<bool>,
    pub controller: Option<bool>,
    pub kind: Kind,
    pub name: StringView,
    pub uid: Uid,
}

impl OwnerReferenceView {
    pub open spec fn is_controller_ref(self) -> bool {
        self.controller.is_Some()
        && self.controller.get_Some_0()
    }
}

pub open spec fn owner_reference_to_object_reference(owner_reference: OwnerReferenceView, namespace: StringView) -> ObjectRef {
    ObjectRef {
        kind: owner_reference.kind,
        namespace: namespace,
        name: owner_reference.name,
    }
}

impl Marshalable for OwnerReferenceView {
    closed spec fn marshal(self) -> Value;

    closed spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

}
