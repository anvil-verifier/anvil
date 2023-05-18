use kube::CustomResource;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::vec;
use k8s_openapi::api::core::v1 as corev1;
use k8s_openapi::apimachinery::pkg::api::resource::Quantity as Quantity;




#[derive(CustomResource, Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[kube(group = "anvil.dev", version = "v1", kind = "RabbitmqCluster")]
#[kube(shortname = "rbmq", namespaced)]
pub struct RabbitmqClusterSpec {
    pub replica: i32,
    #[serde(rename = "image", skip_serializing_if = "Option::is_none")]
    pub image: Option<String>,
    #[serde(rename = "image", skip_serializing_if = "Option::is_none")]
    pub image_pull_secrets: Option<vec::Vec<corev1::LocalObjectReference>>,
    #[serde(rename = "resources", skip_serializing_if = "Option::is_none")]
    pub resources: Option<corev1::ResourceRequirements>,
    #[serde(rename = "persistence", skip_serializing_if = "Option::is_none")]
    pub persistence: Option<RabbitmqClusterPersistenceSpec>,
}

#[derive(Debug, Clone, Deserialize, Serialize, JsonSchema)]
pub struct  RabbitmqClusterPersistenceSpec{
    storage_class_name: Option<String>,
    storage: Option<Quantity>,
}

