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



pub fn headless_build(rabbitmq: &RabbitmqCluster) -> corev1::Service {
    let name_node = rabbitmq.metadata.name.clone().unwrap() + "-node";
    corev1::Service {
        metadata: metav1::ObjectMeta {
            name: Some(name_node),
            namespace: rabbitmq.metadata.namespace.clone(),
            ..Default::default()
        },
        ..Default::default()
    }
}
