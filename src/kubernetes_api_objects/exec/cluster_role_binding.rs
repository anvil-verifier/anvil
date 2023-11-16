// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, common::*, dynamic::*, object_meta::*, resource::*, role_binding::*,
};
use crate::kubernetes_api_objects::spec::{cluster_role_binding::*, resource::*};
use crate::vstd_ext::{string_map::StringMap, string_view::StringView};
use vstd::{prelude::*, seq_lib::*, string::*};

verus! {

/// This definition is a wrapper of ClusterRoleBinding defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/rbac/v1/cluster_role_binding.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/reference/access-authn-authz/rbac/.

#[verifier(external_body)]
pub struct ClusterRoleBinding {
    inner: deps_hack::k8s_openapi::api::rbac::v1::ClusterRoleBinding,
}

impl ClusterRoleBinding {
    pub spec fn view(&self) -> ClusterRoleBindingView;

    #[verifier(external_body)]
    pub fn default() -> (role_binding: ClusterRoleBinding)
        ensures
            role_binding@ == ClusterRoleBindingView::default(),
    {
        ClusterRoleBinding {
            inner: deps_hack::k8s_openapi::api::rbac::v1::ClusterRoleBinding::default(),
        }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn set_metadata(&mut self, metadata: ObjectMeta)
        ensures
            self@ == old(self)@.set_metadata(metadata@),
    {
        self.inner.metadata = metadata.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_role_ref(&mut self, role_ref: RoleRef)
        ensures
            self@ == old(self)@.set_role_ref(role_ref@),
    {
        self.inner.role_ref = role_ref.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_subjects(&mut self, subjects: Vec<Subject>)
        ensures
            self@ == old(self)@.set_subjects(subjects@.map_values(|s: Subject| s@)),
    {
        self.inner.subjects = Some(
            subjects.into_iter().map(|s: Subject| s.into_kube()).collect()
        );
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::rbac::v1::ClusterRoleBinding {
        self.inner
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::rbac::v1::ClusterRoleBinding) -> (role_binding: ClusterRoleBinding)
    {
        ClusterRoleBinding { inner: inner }
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == ClusterRoleBindingView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::rbac::v1::ClusterRoleBinding>(&()))
    }

    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.marshal(),
    {
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<ClusterRoleBinding, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == ClusterRoleBindingView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == ClusterRoleBindingView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::rbac::v1::ClusterRoleBinding>();
        if parse_result.is_ok() {
            let res = ClusterRoleBinding { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

}
