// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::cluster_role::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::kubernetes_api_objects::role::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for cluster role
#[test]
#[verifier(external)]
pub fn test_default() {
    let cluster_role = ClusterRole::default();
    assert_eq!(cluster_role.into_kube(), deps_hack::k8s_openapi::api::rbac::v1::ClusterRole::default());
}

#[test]
#[verifier(external)]
pub fn test_set_metadata() {
    let mut cluster_role = ClusterRole::default();
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    cluster_role.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), cluster_role.into_kube().metadata);
}

#[test]
#[verifier(external)]
pub fn test_metadata() {
    let mut cluster_role = ClusterRole::default();
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    cluster_role.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), cluster_role.metadata().into_kube());
}

#[test]
#[verifier(external)]
pub fn test_set_policy_rules() {
    let mut cluster_role = ClusterRole::default();
    let policy_rules_gen = || {
        let mut policy_rules = Vec::new();
        let mut policy_rule = PolicyRule::default();
        policy_rule.set_api_groups(vec![new_strlit("api_groups").to_string()]);
        policy_rule.set_resources(vec![new_strlit("resources").to_string()]);
        policy_rule.set_verbs(vec![new_strlit("verbs").to_string()]);
        policy_rules.push(policy_rule);
        policy_rules
    };

    cluster_role.set_policy_rules(policy_rules_gen());
    assert_eq!(
        policy_rules_gen()
            .into_iter()
            .map(|s: PolicyRule| s.into_kube())
            .collect::<Vec<_>>(),
        cluster_role.into_kube().rules.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_api_resource(){
    let api_resource = ClusterRole::api_resource();
    assert_eq!(api_resource.into_kube().kind, "ClusterRole");
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_cluster_role = deps_hack::k8s_openapi::api::rbac::v1::ClusterRole {
        metadata:deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                    name: Some("name".to_string()),
                    ..Default::default()
                },
        ..Default::default()
    };
    let cluster_role = ClusterRole::from_kube(
        kube_cluster_role.clone(),
    );
    assert_eq!(cluster_role.into_kube(),
                kube_cluster_role);
}

}
