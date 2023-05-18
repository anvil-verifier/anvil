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


pub fn role_binding_build(rabbitmq: &RabbitmqCluster) -> rbacv1::RoleBinding {
    let name_new = rabbitmq.metadata.name.clone().unwrap() + "-server";
    let name_role = rabbitmq.metadata.name.clone().unwrap() + "-peer-discorvery";
    rbacv1::RoleBinding  {
        metadata: metav1::ObjectMeta {
            name: Some(name_new.clone()),
            namespace: rabbitmq.meta().namespace.clone(),
            labels: Some(BTreeMap::from([(
                "app".to_string(),
                rabbitmq.meta().name.as_ref().unwrap().clone(),
            )])),
            owner_references: Some(vec![rabbitmq.controller_owner_ref(&()).unwrap()]),
            ..metav1::ObjectMeta::default()
        },
        role_ref: rbacv1::RoleRef {
            api_group: "rbac.authorization.k8s.io".to_string(),
            kind: "Role".to_string(),
            name: name_role,
        },
        subjects: Some(vec![rbacv1::Subject {
            kind: "ServiceAccount".to_string(),
            name: name_new,
            namespace: rabbitmq.meta().namespace.clone(),
            ..rbacv1::Subject::default()
        }]),
        ..rbacv1::RoleBinding ::default()
    }
}