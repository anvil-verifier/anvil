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
    let name_new = rabbitmq.metadata.name.clone().unwrap() + "-server-conf";
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
            ("operatorDefaults.conf".to_string(), default_rbmq_config(rabbitmq)),
            ("userDefineConfiguration.conf".to_string(),default_user_config(rabbitmq))
        ])),
        ..corev1::ConfigMap::default()
    }
}


fn default_rbmq_config(rabbitmq: &RabbitmqCluster) -> String {
    let mut default_part = concat!(
        "queue_master_locator = min-masters\n",
        "disk_free_limit.absolute = 2GB\n",
        "cluster_partition_handling = pause_minority\n",
        "cluster_formation.peer_discovery_backend = rabbit_peer_discovery_k8s\n",
        "cluster_formation.k8s.host = kubernetes.default\n",
        "cluster_formation.k8s.address_type = hostname\n",
    ).to_string();
    let rabmq_part = format!(
        "cluster_formation.target_cluster_size_hint = {}\n\
        cluster_name = {}\n",
        rabbitmq.spec.replica,
        rabbitmq.metadata.name.as_ref().unwrap().clone()
    );
    default_part.push_str(&rabmq_part);
    default_part
}

fn default_user_config(rabbitmq: &RabbitmqCluster) -> String {
    let mut value = 0;
    if rabbitmq.spec.resources.is_none() {
        value = remove_headroom(1073741824*2 as i64)
    }
    let rabmq_part = format!(
        "total_memory_available_override_value = {}\n",
        value,
    );
    rabmq_part
}


fn remove_headroom(mem_limit: i64) -> i64 {
    const GIB: i64 = 1073741824;
    if mem_limit / 5 > 2 * GIB {
        return mem_limit - 2 * GIB;
    }
    return mem_limit - mem_limit / 5;
}
