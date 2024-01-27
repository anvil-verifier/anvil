// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, object_meta::*, resource::*,
};
use crate::kubernetes_api_objects::spec::{resource::*, role::*};
use crate::vstd_ext::{string_map::StringMap, string_view::StringView};
use vstd::{prelude::*, seq_lib::*};

verus! {

/// This definition is a wrapper of Role defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/rbac/v1/role.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/reference/access-authn-authz/rbac/.

#[verifier(external_body)]
pub struct Role {
    inner: deps_hack::k8s_openapi::api::rbac::v1::Role,
}

impl View for Role {
    type V = RoleView;

    spec fn view(&self) -> RoleView;
}

impl Role {
    #[verifier(external_body)]
    pub fn default() -> (role: Role)
        ensures role@ == RoleView::default(),
    {
        Role {
            inner: deps_hack::k8s_openapi::api::rbac::v1::Role::default(),
        }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn rules(&self) -> (policy_rules: Option<Vec<PolicyRule>>)
        ensures
            self@.policy_rules.is_Some() == policy_rules.is_Some(),
            policy_rules.is_Some() ==> policy_rules.get_Some_0()@.map_values(|policy_rule: PolicyRule| policy_rule@) == self@.policy_rules.get_Some_0()
    {
        match &self.inner.rules {
            Some(p) => Some(p.into_iter().map(|item| PolicyRule::from_kube(item.clone())).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn set_metadata(&mut self, metadata: ObjectMeta)
        ensures self@ == old(self)@.set_metadata(metadata@),
    {
        self.inner.metadata = metadata.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_rules(&mut self, policy_rules: Vec<PolicyRule>)
        ensures self@ == old(self)@.set_rules(policy_rules@.map_values(|policy_rule: PolicyRule| policy_rule@)),
    {
        self.inner.rules = Some(
            policy_rules.into_iter().map(|p| p.into_kube()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (c: Self)
        ensures c@ == self@,
    {
        Role { inner: self.inner.clone() }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::rbac::v1::Role { self.inner }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::rbac::v1::Role) -> Role { Role { inner: inner } }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures res@.kind == RoleView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::rbac::v1::Role>(&()))
    }

    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures obj@ == self@.marshal(),
    {
        DynamicObject::from_kube(deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap())
    }

    #[verifier(external_body)]
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<Role, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == RoleView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == RoleView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::rbac::v1::Role>();
        if parse_result.is_ok() {
            let res = Role { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

#[verifier(external_body)]
pub struct PolicyRule {
    inner: deps_hack::k8s_openapi::api::rbac::v1::PolicyRule,
}

impl PolicyRule {
    pub spec fn view(&self) -> PolicyRuleView;

    #[verifier(external_body)]
    pub fn default() -> (policy_rule: PolicyRule)
        ensures policy_rule@ == PolicyRuleView::default(),
    {
        PolicyRule {
            inner: deps_hack::k8s_openapi::api::rbac::v1::PolicyRule::default(),
        }
    }

    #[verifier(external_body)]
    pub fn api_groups(&self) -> (api_groups: Option<Vec<String>>)
        ensures
            self@.api_groups.is_Some() == api_groups.is_Some(),
            api_groups.is_Some() ==> api_groups.get_Some_0()@.map_values(|api_group: String| api_group@) == self@.api_groups.get_Some_0()
    {
        match &self.inner.api_groups {
            Some(a) => Some(a.into_iter().map(|item| String::from_rust_string(item.clone())).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn resources(&self) -> (resources: Option<Vec<String>>)
        ensures
            self@.resources.is_Some() == resources.is_Some(),
            resources.is_Some() ==> resources.get_Some_0()@.map_values(|resource: String| resource@) == self@.resources.get_Some_0()
    {
        match &self.inner.resources {
            Some(a) => Some(a.into_iter().map(|item| String::from_rust_string(item.clone())).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn verbs(&self) -> (verbs: Vec<String>)
        ensures
            verbs@.map_values(|verb: String| verb@) == self@.verbs
    {
        self.inner.verbs.clone().into_iter().map(|item| String::from_rust_string(item)).collect()
    }

    #[verifier(external_body)]
    pub fn set_api_groups(&mut self, api_groups: Vec<String>)
        ensures self@ == old(self)@.set_api_groups(api_groups@.map_values(|api_group: String| api_group@)),
    {
        self.inner.api_groups = Some(api_groups.into_iter().map(|a: String| a.into_rust_string()).collect())
    }

    #[verifier(external_body)]
    pub fn set_resources(&mut self, resources: Vec<String>)
        ensures self@ == old(self)@.set_resources(resources@.map_values(|resource: String| resource@)),
    {
        self.inner.resources = Some(resources.into_iter().map(|r: String| r.into_rust_string()).collect())
    }

    #[verifier(external_body)]
    pub fn set_verbs(&mut self, verbs: Vec<String>)
        ensures self@ == old(self)@.set_verbs(verbs@.map_values(|verb: String| verb@)),
    {
        self.inner.verbs = verbs.into_iter().map(|v: String| v.into_rust_string()).collect()
    }


    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::rbac::v1::PolicyRule { self.inner }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::rbac::v1::PolicyRule) -> PolicyRule { PolicyRule { inner: inner } }
}

}
