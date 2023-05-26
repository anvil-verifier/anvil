use crate::rabbitmqcluster_types::RabbitmqCluster;
use k8s_openapi::api::core::v1 as corev1;
use k8s_openapi::api::rbac::v1 as rbacv1;
use k8s_openapi::apimachinery::pkg::api::resource::Quantity;
use k8s_openapi::apimachinery::pkg::apis::meta::v1 as metav1;
use k8s_openapi::apimachinery::pkg::util::intstr::IntOrString;
use k8s_openapi::{api::apps::v1 as appsv1, ByteString};
use kube::{
    api::{Api, ListParams, PostParams},
    runtime::controller::{Action, Controller},
    Client, CustomResourceExt,
};
use kube_client::{self, client};
use kube_core::{self, Resource};
use std::collections::BTreeMap;

pub fn default_user_secret_build(rabbitmq: &RabbitmqCluster) -> corev1::Secret {
    corev1::Secret {
        metadata: metav1::ObjectMeta {
            name: Some(rabbitmq.metadata.name.clone().unwrap() + "-default-user"),
            namespace: rabbitmq.metadata.namespace.clone(),
            owner_references: Some(vec![rabbitmq.controller_owner_ref(&()).unwrap()]),
            ..metav1::ObjectMeta::default()
        },
        type_: Some("Opaque".to_string()),
        data: Some(BTreeMap::from([
            (
                "username".to_string(),
                ByteString("user".to_string().into_bytes()),
            ),
            (
                "password".to_string(),
                ByteString("changeme".to_string().into_bytes()),
            ),
            (
                "type".to_string(),
                ByteString("rabbitmq".to_string().into_bytes()),
            ),
            (
                "host".to_string(),
                ByteString(
                    format!(
                        "{}.{}.svc",
                        rabbitmq.metadata.name.as_ref().unwrap(),
                        rabbitmq.metadata.namespace.as_ref().unwrap()
                    )
                    .into_bytes(),
                ),
            ),
            (
                "provider".to_string(),
                ByteString("rabbitmq".to_string().into_bytes()),
            ),
            (
                "default_user.conf".to_string(),
                ByteString(
                    "default_user = user\ndefault_pass = changeme"
                        .to_string()
                        .into_bytes(),
                ), // not sure how to do this
            ),
            (
                "port".to_string(),
                ByteString("5672".to_string().into_bytes()), // not sure how to do this
            ),
        ])),
        ..corev1::Secret::default()
    }
}
