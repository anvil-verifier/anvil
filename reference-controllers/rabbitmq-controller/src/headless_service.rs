use crate::rabbitmqcluster_types::RabbitmqCluster;
use k8s_openapi::api::core::v1 as corev1;
use k8s_openapi::apimachinery::pkg::apis::meta::v1 as metav1;
use kube_core::Resource;
use std::collections::BTreeMap;

pub fn headless_build(rabbitmq: &RabbitmqCluster) -> corev1::Service {
    let name_node = rabbitmq.metadata.name.clone().unwrap() + "-nodes";
    corev1::Service {
        metadata: metav1::ObjectMeta {
            name: Some(name_node),
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
                    port: 4369,
                    name: Some("epmd".to_string()),
                    ..Default::default()
                },
                corev1::ServicePort {
                    port: 25672,
                    name: Some("cluster-rpc".to_string()),
                    ..Default::default()
                },
            ]),
            publish_not_ready_addresses: Some(true),
            ..corev1::ServiceSpec::default()
        }),
        ..Default::default()
    }
}
