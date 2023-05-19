use k8s_openapi::api::apps::v1 as appsv1;
use k8s_openapi::api::core::v1 as corev1;
use k8s_openapi::apimachinery::pkg::api::resource::Quantity as Quantity;
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


pub fn plugins_configmap_build(rabbitmq: &RabbitmqCluster) -> corev1::ConfigMap{
    let name_new = rabbitmq.metadata.name.clone().unwrap() + "-plugins-conf";
    corev1::ConfigMap {
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
        data: Some(BTreeMap::from([
            ("enabled_plugins".to_string(), "[rabbitmq_peer_discovery_k8s,rabbitmq_prometheus,rabbitmq_management].".to_string()) // default plugins(no additional)
        ])),
        ..corev1::ConfigMap::default()
    }
}

