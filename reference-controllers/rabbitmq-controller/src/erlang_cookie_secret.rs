use base64::encode;
use k8s_openapi::api::apps::v1 as appsv1;
use k8s_openapi::api::core::v1 as corev1;
use k8s_openapi::apimachinery::pkg::api::resource::Quantity;
use k8s_openapi::apimachinery::pkg::apis::meta::v1 as metav1;
use k8s_openapi::ByteString;
use kube::{
    api::{Api, ListParams, PostParams},
    runtime::controller::{Action, Controller},
    Client, CustomResourceExt,
};
use kube_client::{self, client};
use kube_core::{self, Resource};
use rand::Rng;
use std::{collections::BTreeMap, vec};

use crate::rabbitmqcluster_types::RabbitmqCluster;

pub fn erlang_build(rabbitmq: &RabbitmqCluster) -> corev1::Secret {
    let cookie = random_encoded_string(24).into_bytes();
    let name_cookie = rabbitmq.metadata.name.clone().unwrap() + "-erlang-cookie";
    corev1::Secret {
        metadata: metav1::ObjectMeta {
            name: Some(name_cookie),
            namespace: rabbitmq.metadata.namespace.clone(),
            owner_references: Some(vec![rabbitmq.controller_owner_ref(&()).unwrap()]),
            labels: Some(BTreeMap::from([(
                "app".to_string(),
                rabbitmq.meta().name.as_ref().unwrap().clone(),
            )])),
            ..Default::default()
        },
        data: Some(BTreeMap::from([(
            ".erlang.cookie".to_string(),
            ByteString(cookie),
        )])),
        type_: Some("Opaque".to_string()),
        ..Default::default()
    }
}

fn random_encoded_string(data_len: usize) -> String {
    let random_bytes: Vec<u8> = (0..data_len).map(|_| rand::random::<u8>()).collect();
    encode(random_bytes)
}
