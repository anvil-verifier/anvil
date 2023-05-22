use crate::rabbitmqcluster_types::RabbitmqCluster;
use k8s_openapi::api::apps::v1 as appsv1;
use k8s_openapi::api::core::v1 as corev1;
use k8s_openapi::apimachinery::pkg::api::resource::Quantity;
use k8s_openapi::apimachinery::pkg::apis::meta::v1 as metav1;
use k8s_openapi::apimachinery::pkg::util::intstr::IntOrString;
use kube::{
    api::{Api, ListParams, PostParams},
    runtime::controller::{Action, Controller},
    Client, CustomResourceExt,
};
use kube_client::{self, client};
use kube_core::{self, Resource};
use std::collections::BTreeMap;

pub fn plugins_configmap_build(rabbitmq: &RabbitmqCluster) -> corev1::ConfigMap {
    let name = rabbitmq.metadata.name.clone().unwrap() + "-plugins-conf";
    corev1::ConfigMap {
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
        data: Some(BTreeMap::from([
            (
                "enabled_plugins".to_string(),
                "[rabbitmq_peer_discovery_k8s,rabbitmq_management].".to_string(), // rabbitmq_prometheus(default in hello-world, but not necessary)
            ), // default plugins(no additional)
        ])),
        ..corev1::ConfigMap::default()
    }
}
