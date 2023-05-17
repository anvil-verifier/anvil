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


pub fn service_build(rabbitmq: &RabbitmqCluster) -> corev1::Service {
    corev1::Service {
        metadata: metav1::ObjectMeta {
            name: rabbitmq.metadata.name.clone(),
            namespace: rabbitmq.metadata.namespace.clone(),
            owner_references: Some(vec![rabbitmq.controller_owner_ref(&()).unwrap()]),
            labels: Some(BTreeMap::from([(
                "app".to_string(),
                rabbitmq.meta().name.as_ref().unwrap().clone(),
            )])),
            ..metav1::ObjectMeta::default()
        },
        spec: Some(corev1::ServiceSpec {
            type_: Some("ClusterIP".to_string()),
            cluster_ip: Some("None".to_string()),
            selector: Some(BTreeMap::from([(
                "app".to_string(),
                rabbitmq.meta().name.as_ref().unwrap().clone(),
            )])),
            ports: Some(vec![
                corev1::ServicePort {
                    protocol: Some("TCP".to_string()),
                    port: 5672,
                    target_port: Some(IntOrString::Int(5672)),
                    name: Some("amqp".to_string()),
                    app_protocol: Some("amqp".to_string()),
                    node_port: Some(0),
                    ..Default::default()
                },
                corev1::ServicePort {
                    protocol: Some("TCP".to_string()),
                    port: 15672,
                    target_port: Some(IntOrString::Int(15672)),
                    name: Some("management".to_string()),
                    app_protocol: Some("http".to_string()),
                    node_port: Some(0),
                    ..Default::default()
                }, // Other ports need additional plugin enabled
            ]),
            publish_not_ready_addresses: Some(true),
            ..corev1::ServiceSpec::default()
        }),
        ..Default::default()
    }
}
