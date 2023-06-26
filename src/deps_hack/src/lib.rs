pub use anyhow;
pub use base64;
pub use futures;
pub use k8s_openapi;
pub use kube;
pub use kube_client;
pub use kube_core;
pub use kube_derive;
pub use rand;
pub use schemars;
pub use serde;
pub use serde_json;
pub use serde_yaml;
pub use thiserror;
pub use tokio;
pub use tracing;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("MissingObjectKey: {0}")]
    MissingObjectKey(&'static str),
    #[error("APIError")]
    APIError,
}

#[derive(
    kube::CustomResource, Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "SimpleCR")]
#[kube(shortname = "cr", namespaced)]
pub struct SimpleCRSpec {
    pub content: String,
}

#[derive(
    kube::CustomResource, Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "ZookeeperCluster")]
#[kube(shortname = "zk", namespaced)]
pub struct ZookeeperClusterSpec {
    pub replica: i32,
}

#[derive(
    kube::CustomResource, Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "RabbitmqCluster")]
#[kube(shortname = "rbmq", namespaced)]
pub struct RabbitmqClusterSpec {
    pub replicas: i32,
    #[serde(rename = "rabbitmq", skip_serializing_if = "Option::is_none")]
    pub rabbitmq_config: Option<RabbitmqClusterConfigurationSpec>,
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
