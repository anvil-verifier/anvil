use k8s_openapi::api::apps::v1 as appsv1;
use k8s_openapi::api::core::v1 as corev1;
use k8s_openapi::api::rbac::v1 as rbacv1;
use k8s_openapi::apimachinery::pkg::api::resource::Quantity;
use k8s_openapi::apimachinery::pkg::apis::meta::v1 as metav1;
use kube::{
    api::{Api, ListParams, PostParams},
    runtime::controller::{Action, Controller},
    Client, CustomResourceExt,
};
use kube_client::{self, client};
use kube_core::{self, Resource};
use std::collections::BTreeMap;
use crate::rabbitmqcluster_types::RabbitmqCluster;
use k8s_openapi::apimachinery::pkg::util::intstr::IntOrString;


pub fn role_build(rabbitmq: &RabbitmqCluster) -> rbacv1::Role {
    let name_new = rabbitmq.metadata.name.clone().unwrap() + "-peer-discorvery";
    rbacv1::Role {
        metadata: metav1::ObjectMeta {
            name: Some(name_new),
            namespace: rabbitmq.meta().namespace.clone(),
            labels: Some(BTreeMap::from([(
                "app".to_string(),
                rabbitmq.meta().name.as_ref().unwrap().clone(),
            )])),
            owner_references: Some(vec![rabbitmq.controller_owner_ref(&()).unwrap()]),
            ..metav1::ObjectMeta::default()
        },
        rules:Some( vec![
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
            }] ),
        ..rbacv1::Role::default()
    }
}