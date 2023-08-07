// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::resource::*;
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

    #[verifier(external_body)]
    pub fn default() -> (object_meta: OwnerReference)
        ensures
            object_meta@ == OwnerReferenceView::default(),
    {
        OwnerReference {
            inner: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_api_version(&mut self, api_version: String)
        ensures
            self@ == old(self)@.set_api_version(api_version@),
    {
        self.inner.api_version = api_version.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_block_owner_deletion(&mut self, block_owner_deletion: bool)
        ensures
            self@ == old(self)@.set_block_owner_deletion(block_owner_deletion),
    {
        self.inner.block_owner_deletion = std::option::Option::Some(block_owner_deletion);
    }

    #[verifier(external_body)]
    pub fn set_controller(&mut self, controller: bool)
        ensures
            self@ == old(self)@.set_controller(controller),
    {
        self.inner.controller = std::option::Option::Some(controller);
    }

    #[verifier(external_body)]
    pub fn set_kind(&mut self, kind: String)
        ensures
            self@ == old(self)@.set_kind(kind@),
    {
        self.inner.kind = kind.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = name.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_uid(&mut self, uid: String)
        ensures
            self@ == old(self)@.set_uid(uid@),
    {
        self.inner.uid = uid.into_rust_string();
    }
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
    pub api_version: StringView,
    pub block_owner_deletion: Option<bool>,
    pub controller: Option<bool>,
    pub kind: StringView,
    pub name: StringView,
    pub uid: StringView,
}

impl OwnerReferenceView {
    #[verifier(external_body)]
    pub open spec fn default() -> OwnerReferenceView {
        OwnerReferenceView {
            api_version: new_strlit("")@,
            block_owner_deletion: Option::None,
            controller: Option::None,
            kind: new_strlit("")@,
            name: new_strlit("")@,
            uid: new_strlit("")@,
        }
    }

    #[verifier(external_body)]
    pub open spec fn set_api_version(self, api_version: StringView) -> OwnerReferenceView
    {
        OwnerReferenceView {
            api_version: api_version,
            ..self
        }
    }

    #[verifier(external_body)]
    pub open spec fn set_block_owner_deletion(self, block_owner_deletion: bool) -> OwnerReferenceView
    {
        OwnerReferenceView {
            block_owner_deletion: Some(block_owner_deletion),
            ..self
        }
    }

    #[verifier(external_body)]
    pub open spec fn set_controller(self, controller: bool) -> OwnerReferenceView
    {
        OwnerReferenceView {
            controller: Some(controller),
            ..self
        }
    }

    #[verifier(external_body)]
    pub open spec fn set_kind(self, kind: StringView) -> OwnerReferenceView
    {
        OwnerReferenceView {
            kind: kind,
            ..self
        }
    }

    #[verifier(external_body)]
    pub open spec fn set_name(self, name: StringView) -> OwnerReferenceView
    {
        OwnerReferenceView {
            name: name,
            ..self
        }
    }

    #[verifier(external_body)]
    pub open spec fn set_uid(self, uid: StringView) -> OwnerReferenceView
    {
        OwnerReferenceView {
            uid: uid,
            ..self
        }
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
