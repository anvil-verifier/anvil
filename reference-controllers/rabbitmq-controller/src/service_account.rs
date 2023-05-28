use k8s_openapi::api::apps::v1 as appsv1;
use k8s_openapi::api::core::v1 as corev1;
use k8s_openapi::apimachinery::pkg::api::resource::Quantity;
use k8s_openapi::apimachinery::pkg::apis::meta::v1 as metav1;
use kube::{
    api::{Api, ListParams, PostParams},
    runtime::controller::{Action, Controller},
    Client, CustomResourceExt,
};
use kube_client::{self, client};
use kube_core::{self, Resource};

use crate::rabbitmqcluster_types::RabbitmqCluster;
use k8s_openapi::apimachinery::pkg::util::intstr::IntOrString;
use std::collections::BTreeMap;

pub fn service_account_build(rabbitmq: &RabbitmqCluster) -> corev1::ServiceAccount {
    let name = rabbitmq.metadata.name.clone().unwrap() + "-server";
    corev1::ServiceAccount {
        metadata: metav1::ObjectMeta {
            name: Some(name),
            namespace: rabbitmq.metadata.namespace.clone(),
            owner_references: Some(vec![rabbitmq.controller_owner_ref(&()).unwrap()]),
            labels: Some(BTreeMap::from([(
                "app".to_string(),
                rabbitmq.meta().name.as_ref().unwrap().clone(),
            )])),
            ..metav1::ObjectMeta::default()
        },
        ..corev1::ServiceAccount::default()
    }
}
