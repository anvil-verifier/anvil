// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, object_meta::*, resource::*,
};
use crate::kubernetes_api_objects::spec::{resource::*, role::*};
use vstd::prelude::*;

// This definition is a wrapper of Role defined at
// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/rbac/v1/role.rs.
// It is supposed to be used in exec controller code.
//
// More detailed information: https://kubernetes.io/docs/reference/access-authn-authz/rbac/.

implement_object_wrapper_type!(Role, deps_hack::k8s_openapi::api::rbac::v1::Role, RoleView);

verus! {

impl Role {
    #[verifier(external_body)]
    pub fn rules(&self) -> (policy_rules: Option<Vec<PolicyRule>>)
        ensures
            self@.policy_rules is Some == policy_rules is Some,
            policy_rules is Some ==> policy_rules->0@.map_values(|policy_rule: PolicyRule| policy_rule@) == self@.policy_rules->0
    {
        match &self.inner.rules {
            Some(p) => Some(p.into_iter().map(|item| PolicyRule::from_kube(item.clone())).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn set_rules(&mut self, policy_rules: Vec<PolicyRule>)
        ensures self@ == old(self)@.with_rules(policy_rules@.map_values(|policy_rule: PolicyRule| policy_rule@)),
    {
        self.inner.rules = Some(
            policy_rules.into_iter().map(|p| p.into_kube()).collect()
        )
    }
}

#[verifier(external_body)]
pub struct PolicyRule {
    inner: deps_hack::k8s_openapi::api::rbac::v1::PolicyRule,
}

impl PolicyRule {
    pub uninterp spec fn view(&self) -> PolicyRuleView;

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
            self@.api_groups is Some == api_groups is Some,
            api_groups is Some ==> api_groups->0@.map_values(|api_group: String| api_group@) == self@.api_groups->0
    {
        self.inner.api_groups.clone()
    }

    #[verifier(external_body)]
    pub fn resources(&self) -> (resources: Option<Vec<String>>)
        ensures
            self@.resources is Some == resources is Some,
            resources is Some ==> resources->0@.map_values(|resource: String| resource@) == self@.resources->0
    {
        self.inner.resources.clone()
    }

    #[verifier(external_body)]
    pub fn verbs(&self) -> (verbs: Vec<String>)
        ensures
            verbs@.map_values(|verb: String| verb@) == self@.verbs
    {
        self.inner.verbs.clone()
    }

    #[verifier(external_body)]
    pub fn set_api_groups(&mut self, api_groups: Vec<String>)
        ensures self@ == old(self)@.with_api_groups(api_groups@.map_values(|api_group: String| api_group@)),
    {
        self.inner.api_groups = Some(api_groups)
    }

    #[verifier(external_body)]
    pub fn set_resources(&mut self, resources: Vec<String>)
        ensures self@ == old(self)@.with_resources(resources@.map_values(|resource: String| resource@)),
    {
        self.inner.resources = Some(resources)
    }

    #[verifier(external_body)]
    pub fn set_verbs(&mut self, verbs: Vec<String>)
        ensures self@ == old(self)@.with_verbs(verbs@.map_values(|verb: String| verb@)),
    {
        self.inner.verbs = verbs
    }
}

}

implement_resource_wrapper_trait!(
    PolicyRule,
    deps_hack::k8s_openapi::api::rbac::v1::PolicyRule
);
