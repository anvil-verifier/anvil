use k8s_openapi::api::core::v1 as corev1;
use k8s_openapi::apimachinery::pkg::api::resource::Quantity;
use kube::CustomResource;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::vec;

#[derive(CustomResource, Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[kube(group = "anvil.dev", version = "v1", kind = "RabbitmqCluster")]
#[kube(shortname = "rbmq", namespaced)]
pub struct RabbitmqClusterSpec {
    pub replicas: i32,
    #[serde(rename = "image", skip_serializing_if = "Option::is_none")]
    pub image: Option<String>,
    #[serde(rename = "rabbitmq", skip_serializing_if = "Option::is_none")]
    pub rabbitmq_config: Option<RabbitmqClusterConfigurationSpec>,
}

#[derive(Debug, Clone, Deserialize, Serialize, JsonSchema)]
pub struct RabbitmqClusterPersistenceSpec {
    pub storage_class_name: Option<String>,
    pub storage: Option<Quantity>,
}

#[derive(Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema)]
pub struct RabbitmqClusterConfigurationSpec {
    // #[serde(rename = "additionalPlugins", skip_serializing_if = "Option::is_none")]
    // pub additional_plugins: Option<Vec<String>>,
    #[serde(rename = "additionalConfig", skip_serializing_if = "Option::is_none")]
    pub additional_config: Option<String>,
    #[serde(rename = "advancedConfig", skip_serializing_if = "Option::is_none")]
    pub advanced_config: Option<String>,
    #[serde(rename = "envConfig", skip_serializing_if = "Option::is_none")]
    pub env_config: Option<String>,
}
