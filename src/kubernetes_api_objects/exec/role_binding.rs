// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, object_meta::*, resource::*,
};
use crate::kubernetes_api_objects::spec::{resource::*, role_binding::*};
use vstd::prelude::*;

// This definition is a wrapper of RoleBinding defined at
// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/rbac/v1/role_binding.rs.
// It is supposed to be used in exec controller code.
//
// More detailed information: https://kubernetes.io/docs/reference/access-authn-authz/rbac/.

implement_object_wrapper_type!(
    RoleBinding,
    deps_hack::k8s_openapi::api::rbac::v1::RoleBinding,
    RoleBindingView
);

verus! {

impl RoleBinding {
    #[verifier(external_body)]
    pub fn role_ref(&self) -> (role_ref: RoleRef)
        ensures role_ref@ == self@.role_ref,
    {
        RoleRef::from_kube(self.inner.role_ref.clone())
    }

    #[verifier(external_body)]
    pub fn set_role_ref(&mut self, role_ref: RoleRef)
        ensures self@ == old(self)@.with_role_ref(role_ref@),
    {
        self.inner.role_ref = role_ref.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_subjects(&mut self, subjects: Vec<Subject>)
        ensures self@ == old(self)@.with_subjects(subjects@.map_values(|s: Subject| s@)),
    {
        self.inner.subjects = Some(
            subjects.into_iter().map(|s: Subject| s.into_kube()).collect()
        );
    }
}

#[verifier(external_body)]
pub struct RoleRef {
    inner: deps_hack::k8s_openapi::api::rbac::v1::RoleRef,
}

impl RoleRef {
    pub uninterp spec fn view(&self) -> RoleRefView;

    #[verifier(external_body)]
    pub fn default() -> (role_ref: RoleRef)
        ensures role_ref@ == RoleRefView::default(),
    {
        RoleRef { inner: deps_hack::k8s_openapi::api::rbac::v1::RoleRef::default() }
    }

    #[verifier(external_body)]
    pub fn eq(&self, other: &Self) -> (b: bool)
        ensures b == (self.view() == other.view())
    {
        self.inner == other.inner
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (c: Self)
        ensures c@ == self@,
    {
        RoleRef { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn api_group(&self) -> (api_group: String)
        ensures api_group@ == self@.api_group
    {
        self.inner.api_group.clone()
    }

    #[verifier(external_body)]
    pub fn kind(&self) -> (kind: String)
        ensures kind@ == self@.kind
    {
        self.inner.kind.clone()
    }

    #[verifier(external_body)]
    pub fn set_api_group(&mut self, api_group: String)
        ensures self@ == old(self)@.with_api_group(api_group@),
    {
        self.inner.api_group = api_group;
    }

    #[verifier(external_body)]
    pub fn set_kind(&mut self, kind: String)
        ensures self@ == old(self)@.with_kind(kind@),
    {
        self.inner.kind = kind;
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.with_name(name@),
    {
        self.inner.name = name;
    }
}

#[verifier(external_body)]
pub struct Subject {
    inner: deps_hack::k8s_openapi::api::rbac::v1::Subject,
}

impl Subject {
    pub uninterp spec fn view(&self) -> SubjectView;

    #[verifier(external_body)]
    pub fn default() -> (subject: Subject)
        ensures subject@ == SubjectView::default(),
    {
        Subject {
            inner: deps_hack::k8s_openapi::api::rbac::v1::Subject::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_kind(&mut self, kind: String)
        ensures self@ == old(self)@.with_kind(kind@),
    {
        self.inner.kind = kind;
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.with_name(name@),
    {
        self.inner.name = name;
    }

    #[verifier(external_body)]
    pub fn set_namespace(&mut self, namespace: String)
        ensures self@ == old(self)@.with_namespace(namespace@),
    {
        self.inner.namespace = Some(namespace);
    }
}

}

implement_resource_wrapper_trait!(RoleRef, deps_hack::k8s_openapi::api::rbac::v1::RoleRef);

implement_resource_wrapper_trait!(Subject, deps_hack::k8s_openapi::api::rbac::v1::Subject);
