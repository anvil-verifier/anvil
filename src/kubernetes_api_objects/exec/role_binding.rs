// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, object_meta::*, resource::*,
};
use crate::kubernetes_api_objects::spec::{resource::*, role_binding::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::StringView;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {


/// This definition is a wrapper of RoleBinding defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/rbac/v1/role_binding.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/reference/access-authn-authz/rbac/.

#[verifier(external_body)]
pub struct RoleBinding {
    inner: deps_hack::k8s_openapi::api::rbac::v1::RoleBinding,
}

impl View for RoleBinding {
    type V = RoleBindingView;

    spec fn view(&self) -> RoleBindingView;
}

impl RoleBinding {
    #[verifier(external_body)]
    pub fn default() -> (role_binding: RoleBinding)
        ensures role_binding@ == RoleBindingView::default(),
    {
        RoleBinding {
            inner: deps_hack::k8s_openapi::api::rbac::v1::RoleBinding::default(),
        }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn role_ref(&self) -> (role_ref: RoleRef)
        ensures role_ref@ == self@.role_ref,
    {
        RoleRef::from_kube(self.inner.role_ref.clone())
    }

    #[verifier(external_body)]
    pub fn set_metadata(&mut self, metadata: ObjectMeta)
        ensures self@ == old(self)@.set_metadata(metadata@),
    {
        self.inner.metadata = metadata.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_role_ref(&mut self, role_ref: RoleRef)
        ensures self@ == old(self)@.set_role_ref(role_ref@),
    {
        self.inner.role_ref = role_ref.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_subjects(&mut self, subjects: Vec<Subject>)
        ensures self@ == old(self)@.set_subjects(subjects@.map_values(|s: Subject| s@)),
    {
        self.inner.subjects = Some(
            subjects.into_iter().map(|s: Subject| s.into_kube()).collect()
        );
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (c: Self)
        ensures c@ == self@,
    {
        RoleBinding { inner: self.inner.clone() }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::rbac::v1::RoleBinding { self.inner }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::rbac::v1::RoleBinding) -> RoleBinding { RoleBinding { inner: inner } }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures res@.kind == RoleBindingView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::rbac::v1::RoleBinding>(&()))
    }

    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures obj@ == self@.marshal(),
    {
        DynamicObject::from_kube(deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap())
    }

    #[verifier(external_body)]
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<RoleBinding, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == RoleBindingView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == RoleBindingView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::rbac::v1::RoleBinding>();
        if parse_result.is_ok() {
            let res = RoleBinding { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

#[verifier(external_body)]
pub struct RoleRef {
    inner: deps_hack::k8s_openapi::api::rbac::v1::RoleRef,
}

impl RoleRef {
    pub spec fn view(&self) -> RoleRefView;

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
        String::from_rust_string(self.inner.api_group.to_string())
    }

    #[verifier(external_body)]
    pub fn kind(&self) -> (kind: String)
        ensures kind@ == self@.kind
    {
        String::from_rust_string(self.inner.kind.to_string())
    }


    #[verifier(external_body)]
    pub fn set_api_group(&mut self, api_group: String)
        ensures self@ == old(self)@.set_api_group(api_group@),
    {
        self.inner.api_group = api_group.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_kind(&mut self, kind: String)
        ensures self@ == old(self)@.set_kind(kind@),
    {
        self.inner.kind = kind.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.set_name(name@),
    {
        self.inner.name = name.into_rust_string();
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::rbac::v1::RoleRef { self.inner }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::rbac::v1::RoleRef) -> RoleRef { RoleRef { inner: inner } }
}

#[verifier(external_body)]
pub struct Subject {
    inner: deps_hack::k8s_openapi::api::rbac::v1::Subject,
}

impl Subject {
    pub spec fn view(&self) -> SubjectView;

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
        ensures self@ == old(self)@.set_kind(kind@),
    {
        self.inner.kind = kind.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.set_name(name@),
    {
        self.inner.name = name.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_namespace(&mut self, namespace: String)
        ensures self@ == old(self)@.set_namespace(namespace@),
    {
        self.inner.namespace = Some(namespace.into_rust_string());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::rbac::v1::Subject { self.inner }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::rbac::v1::Subject) -> Subject { Subject { inner: inner } }
}

}
