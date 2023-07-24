use crate::rabbitmqcluster_types::RabbitmqCluster;
use k8s_openapi::api::rbac::v1 as rbacv1;
use k8s_openapi::apimachinery::pkg::apis::meta::v1 as metav1;
use kube_core::Resource;
use std::collections::BTreeMap;

pub fn role_binding_build(rabbitmq: &RabbitmqCluster) -> rbacv1::RoleBinding {
    let role_binding_name = rabbitmq.metadata.name.clone().unwrap() + "-server";
    let role_name = rabbitmq.metadata.name.clone().unwrap() + "-peer-discovery";
    rbacv1::RoleBinding {
        metadata: metav1::ObjectMeta {
            name: Some(role_binding_name.clone()),
            namespace: rabbitmq.meta().namespace.clone(),
            labels: Some(BTreeMap::from([(
                "app".to_string(),
                rabbitmq.meta().name.as_ref().unwrap().clone(),
            )])),
            owner_references: Some(vec![rabbitmq.controller_owner_ref(&()).unwrap()]),
            ..metav1::ObjectMeta::default()
        },
        role_ref: rbacv1::RoleRef {
            api_group: "rbac.authorization.k8s.io".to_string(),
            kind: "Role".to_string(),
            name: role_name,
        },
        subjects: Some(vec![rbacv1::Subject {
            kind: "ServiceAccount".to_string(),
            name: role_binding_name,
            namespace: rabbitmq.meta().namespace.clone(),
            ..rbacv1::Subject::default()
        }]),
        ..rbacv1::RoleBinding::default()
    }
}
