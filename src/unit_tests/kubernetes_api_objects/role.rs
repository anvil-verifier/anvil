// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::role::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for role
#[test]
#[verifier(external)]
pub fn test_default() {
    let role = Role::default();
    assert_eq!(role.into_kube(), deps_hack::k8s_openapi::api::rbac::v1::Role::default());
}

#[test]
#[verifier(external)]
pub fn test_set_metadata() {
    let mut role = Role::default();
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    role.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), role.into_kube().metadata);
}

#[test]
#[verifier(external)]
pub fn test_metadata() {
    let mut role = Role::default();
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    role.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), role.metadata().into_kube());
}

#[test]
#[verifier(external)]
pub fn test_set_rules() {
    let mut role = Role::default();
    let policy_rule_gen = || {
        let mut policy_rule_1 = PolicyRule::default();
        let mut policy_rule_2 = PolicyRule::default();
        let mut policy_rules = Vec::new();
        let api_groups_gen = |suffix: &str| {
            let api_groups_1 = new_strlit(&format!("api_groups_{}_1", suffix)).to_string();
            let api_groups_2 = new_strlit(&format!("api_groups_{}_2", suffix)).to_string();
            let mut api_groups = Vec::new();
            api_groups.push(api_groups_1);
            api_groups.push(api_groups_2);
            api_groups
        };
        let resources_gen = |suffix: &str| {
            let resources_1 = new_strlit(&format!("resources_{}_1", suffix)).to_string();
            let resources_2 = new_strlit(&format!("resources_{}_2", suffix)).to_string();
            let mut resources = Vec::new();
            resources.push(resources_1);
            resources.push(resources_2);
            resources
        };
        let verbs_gen = |suffix: &str| {
            let verbs_1 = new_strlit(&format!("verbs_{}_1", suffix)).to_string();
            let verbs_2 = new_strlit(&format!("verbs_{}_2", suffix)).to_string();
            let mut verbs = Vec::new();
            verbs.push(verbs_1);
            verbs.push(verbs_2);
            verbs
        };
        policy_rule_1.set_api_groups(api_groups_gen("1"));
        policy_rule_1.set_resources(resources_gen("1"));
        policy_rule_1.set_verbs(verbs_gen("1"));
        policy_rule_2.set_api_groups(api_groups_gen("2"));
        policy_rule_2.set_resources(resources_gen("2"));
        policy_rule_2.set_verbs(verbs_gen("2"));
        policy_rules.push(policy_rule_1);
        policy_rules.push(policy_rule_2);
        policy_rules
    };
    role.set_rules(policy_rule_gen());
    assert_eq!(
        policy_rule_gen()
            .into_iter()
            .map(|s: PolicyRule| s.into_kube())
            .collect::<Vec<_>>(),
        role.into_kube().rules.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut role = Role::default();
    let mut object_meta = ObjectMeta::default();
    let policy_rule_gen = || {
        let mut policy_rule_1 = PolicyRule::default();
        let mut policy_rule_2 = PolicyRule::default();
        let mut policy_rules = Vec::new();
        let api_groups_gen = |suffix: &str| {
            let api_groups_1 = new_strlit(&format!("api_groups_{}_1", suffix)).to_string();
            let api_groups_2 = new_strlit(&format!("api_groups_{}_2", suffix)).to_string();
            let mut api_groups = Vec::new();
            api_groups.push(api_groups_1);
            api_groups.push(api_groups_2);
            api_groups
        };
        let resources_gen = |suffix: &str| {
            let resources_1 = new_strlit(&format!("resources_{}_1", suffix)).to_string();
            let resources_2 = new_strlit(&format!("resources_{}_2", suffix)).to_string();
            let mut resources = Vec::new();
            resources.push(resources_1);
            resources.push(resources_2);
            resources
        };
        let verbs_gen = |suffix: &str| {
            let verbs_1 = new_strlit(&format!("verbs_{}_1", suffix)).to_string();
            let verbs_2 = new_strlit(&format!("verbs_{}_2", suffix)).to_string();
            let mut verbs = Vec::new();
            verbs.push(verbs_1);
            verbs.push(verbs_2);
            verbs
        };
        policy_rule_1.set_api_groups(api_groups_gen("1"));
        policy_rule_1.set_resources(resources_gen("1"));
        policy_rule_1.set_verbs(verbs_gen("1"));
        policy_rule_2.set_api_groups(api_groups_gen("2"));
        policy_rule_2.set_resources(resources_gen("2"));
        policy_rule_2.set_verbs(verbs_gen("2"));
        policy_rules.push(policy_rule_1);
        policy_rules.push(policy_rule_2);
        policy_rules
    };
    object_meta.set_name(new_strlit("name").to_string());
    object_meta.set_namespace(new_strlit("namespace").to_string());
    role.set_metadata(object_meta.clone());
    role.set_rules(policy_rule_gen());
    let role_clone = role.clone();
    assert_eq!(role.into_kube(), role_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_api_resource(){
    let api_resource = Role::api_resource();
    assert_eq!(api_resource.into_kube().kind, "Role");
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_role =
        deps_hack::k8s_openapi::api::rbac::v1::Role {
            metadata: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                name: Some("name".to_string()),
                namespace: Some("namespace".to_string()),
                ..Default::default()
            },
            rules: Some(
                vec![
                    deps_hack::k8s_openapi::api::rbac::v1::PolicyRule {
                        api_groups: Some(vec!["api_groups_1_1".to_string(), "api_groups_1_2".to_string()]),
                        resources: Some(vec!["resources_1_1".to_string(), "resources_1_2".to_string()]),
                        verbs: vec!["verbs_1_1".to_string(), "verbs_1_2".to_string()],
                        ..Default::default()
                    },
                    deps_hack::k8s_openapi::api::rbac::v1::PolicyRule {
                        api_groups: Some(vec!["api_groups_2_1".to_string(), "api_groups_2_2".to_string()]),
                        resources: Some(vec!["resources_2_1".to_string(), "resources_2_2".to_string()]),
                        verbs: vec!["verbs_2_1".to_string(), "verbs_2_2".to_string()],
                        ..Default::default()
                    }
                ]
            ),
            ..Default::default()
        };

    let role = Role::from_kube(kube_role.clone());

    assert_eq!(
        role.into_kube(),
        kube_role
    );
}

#[test]
#[verifier(external)]
pub fn test_marshal() {
    let kube_role =
        deps_hack::k8s_openapi::api::rbac::v1::Role {
            metadata: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                name: Some("name".to_string()),
                namespace: Some("namespace".to_string()),
                ..Default::default()
            },
            rules: Some(
                vec![
                    deps_hack::k8s_openapi::api::rbac::v1::PolicyRule {
                        api_groups: Some(vec!["api_groups_1_1".to_string(), "api_groups_1_2".to_string()]),
                        resources: Some(vec!["resources_1_1".to_string(), "resources_1_2".to_string()]),
                        verbs: vec!["verbs_1_1".to_string(), "verbs_1_2".to_string()],
                        ..Default::default()
                    },
                    deps_hack::k8s_openapi::api::rbac::v1::PolicyRule {
                        api_groups: Some(vec!["api_groups_2_1".to_string(), "api_groups_2_2".to_string()]),
                        resources: Some(vec!["resources_2_1".to_string(), "resources_2_2".to_string()]),
                        verbs: vec!["verbs_2_1".to_string(), "verbs_2_2".to_string()],
                        ..Default::default()
                    }
                ]
            ),
            ..Default::default()
        };

    let role = Role::from_kube(kube_role.clone());

    assert_eq!(
        kube_role,
        Role::unmarshal(role.marshal()).unwrap().into_kube()
    );
}
}
