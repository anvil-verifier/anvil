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
use std::collections::BTreeMap;
use crate::rabbitmqcluster_types::RabbitmqCluster;
use k8s_openapi::apimachinery::pkg::util::intstr::IntOrString;


pub fn server_configmap_build(rabbitmq: &RabbitmqCluster) -> corev1::ConfigMap{
    let name_node = rabbitmq.metadata.name.clone().unwrap() + "-server-conf";
    corev1::ConfigMap {
        metadata: metav1::ObjectMeta {
            name: Some(rabbitmq.meta().name.as_ref().unwrap().clone() + "-configmap"),
            namespace: rabbitmq.meta().namespace.clone(),
            labels: Some(BTreeMap::from([(
                "app".to_string(),
                rabbitmq.meta().name.as_ref().unwrap().clone(),
            )])),
            owner_references: Some(vec![rabbitmq.controller_owner_ref(&()).unwrap()]),
            ..ObjectMeta::default()
        },
        data: Some(BTreeMap::from([
            ("zoo.cfg".to_string(), make_rabbitmq_config()),
            ("log4j.properties".to_string(), make_log4j_config()),
            (
                "log4j-quiet.properties".to_string(),
                make_log4j_quiet_config(),
            ),
            ("env.sh".to_string(), make_env_config(rabbitmq)),
        ])),
        ..corev1::ConfigMap::default()
    }
}


fn default_rbmq_config() -> String {
    concat!(
        "queue_master_locator = min-masters\n",
        "disk_free_limit.absolute = 2GB\n",
        "cluster_partition_handling = pause_minority\n",
        "cluster_formation.peer_discovery_backend = rabbit_peer_discovery_k8s\n",
        "cluster_formation.k8s.host = kubernetes.default\n",
        "cluster_formation.k8s.address_type = hostname\n",
    ).to_string()
}
