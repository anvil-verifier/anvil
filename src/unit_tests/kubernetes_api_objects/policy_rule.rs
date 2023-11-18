// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::role::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for policy rule
#[test]
#[verifier(external)]
pub fn test_default() {
    let policy_rule = PolicyRule::default();
    assert_eq!(policy_rule.into_kube(), deps_hack::k8s_openapi::api::rbac::v1::PolicyRule::default());
}

#[test]
#[verifier(external)]
pub fn test_set_api_groups() {
    let mut policy_rule = PolicyRule::default();
    let api_groups_gen = || {
        let api_groups_1 = new_strlit("api_groups1").to_string();
        let api_groups_2 = new_strlit("api_groups2").to_string();
        let mut api_groups = Vec::new();
        api_groups.push(api_groups_1);
        api_groups.push(api_groups_2);
        api_groups
    };
    policy_rule.set_api_groups(api_groups_gen());
    assert_eq!(
        api_groups_gen()
            .into_iter()
            .map(|s: String| s.into_rust_string())
            .collect::<Vec<_>>(),
        policy_rule.into_kube().api_groups.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_set_resources() {
    let mut policy_rule = PolicyRule::default();
    let resources_gen = || {
        let resources_1 = new_strlit("resources1").to_string();
        let resources_2 = new_strlit("resources2").to_string();
        let mut resources = Vec::new();
        resources.push(resources_1);
        resources.push(resources_2);
        resources
    };
    policy_rule.set_resources(resources_gen());
    assert_eq!(
        resources_gen()
            .into_iter()
            .map(|s: String| s.into_rust_string())
            .collect::<Vec<_>>(),
        policy_rule.into_kube().resources.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_set_verbs() {
    let mut policy_rule = PolicyRule::default();
    let verbs_gen = || {
        let verbs_1 = new_strlit("verbs1").to_string();
        let verbs_2 = new_strlit("verbs2").to_string();
        let mut verbs = Vec::new();
        verbs.push(verbs_1);
        verbs.push(verbs_2);
        verbs
    };
    policy_rule.set_verbs(verbs_gen());
    assert_eq!(
        verbs_gen()
            .into_iter()
            .map(|s: String| s.into_rust_string())
            .collect::<Vec<_>>(),
        policy_rule.into_kube().verbs
    );
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_policy_rule =
        deps_hack::k8s_openapi::api::rbac::v1::PolicyRule {
            api_groups: Some(vec!["api_groups".to_string()]),
            resources: Some(vec!["resources".to_string()]),
            verbs: vec!["verbs".to_string()],
            ..Default::default()
        };

    let policy_rule = PolicyRule::from_kube(kube_policy_rule.clone());

    assert_eq!(
        policy_rule.into_kube(),
        kube_policy_rule
    );
}
}
