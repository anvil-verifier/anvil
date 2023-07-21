use crate::rabbitmqcluster_types::RabbitmqCluster;
use k8s_openapi::api::rbac::v1 as rbacv1;
use k8s_openapi::apimachinery::pkg::apis::meta::v1 as metav1;
use kube_core::Resource;
use std::collections::BTreeMap;

pub fn role_build(rabbitmq: &RabbitmqCluster) -> rbacv1::Role {
    let name = rabbitmq.metadata.name.clone().unwrap() + "-peer-discovery";
    rbacv1::Role {
        metadata: metav1::ObjectMeta {
            name: Some(name),
            namespace: rabbitmq.meta().namespace.clone(),
            labels: Some(BTreeMap::from([(
                "app".to_string(),
                rabbitmq.meta().name.as_ref().unwrap().clone(),
            )])),
            owner_references: Some(vec![rabbitmq.controller_owner_ref(&()).unwrap()]),
            ..metav1::ObjectMeta::default()
        },
        rules: Some(vec![
            rbacv1::PolicyRule {
                api_groups: Some(vec!["".to_string()]),
                resources: Some(vec!["endpoints".to_string()]),
                verbs: vec!["get".to_string()],
                ..Default::default()
            },
            rbacv1::PolicyRule {
                api_groups: Some(vec!["".to_string()]),
                resources: Some(vec!["events".to_string()]),
                verbs: vec!["create".to_string()],
                ..Default::default()
            },
        ]),
        ..rbacv1::Role::default()
    }
}
