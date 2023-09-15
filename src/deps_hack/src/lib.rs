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
pub use zookeeper;

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
    pub replicas: i32,
    pub image: String,
    pub ports: ZookeeperPorts,
    pub conf: ZookeeperConfig,
    #[serde(default)]
    pub resources: k8s_openapi::api::core::v1::ResourceRequirements,
}

#[derive(Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema)]
pub struct ZookeeperPorts {
    #[serde(rename = "client")]
    pub client: i32,
    #[serde(rename = "quorum")]
    pub quorum: i32,
    #[serde(rename = "leaderElection")]
    pub leader_election: i32,
    #[serde(rename = "metrics")]
    pub metrics: i32,
    #[serde(rename = "adminServer")]
    pub admin_server: i32,
}

#[derive(Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema)]
pub struct ZookeeperConfig {
    #[serde(rename = "initLimit")]
    pub init_limit: i32,
    #[serde(rename = "tickTime")]
    pub tick_time: i32,
    #[serde(rename = "syncLimit")]
    pub sync_limit: i32,
    #[serde(rename = "globalOutstandingLimit")]
    pub global_outstanding_limit: i32,
    #[serde(rename = "preAllocSize")]
    pub pre_alloc_size: i32,
    #[serde(rename = "snapCount")]
    pub snap_count: i32,
    #[serde(rename = "commitLogCount")]
    pub commit_log_count: i32,
    #[serde(rename = "snapSizeLimitInKb")]
    pub snap_size_limit_in_kb: i32,
    #[serde(rename = "maxCnxns")]
    pub max_cnxns: i32,
    #[serde(rename = "maxClientCnxns")]
    pub max_client_cnxns: i32,
    #[serde(rename = "minSessionTimeout")]
    pub min_session_timeout: i32,
    #[serde(rename = "maxSessionTimeout")]
    pub max_session_timeout: i32,
    #[serde(rename = "autoPurgeSnapRetainCount")]
    pub auto_purge_snap_retain_count: i32,
    #[serde(rename = "autoPurgePurgeInterval")]
    pub auto_purge_purge_interval: i32,
    #[serde(rename = "quorumListenOnAllIps")]
    pub quorum_listen_on_all_ips: bool,
}

#[derive(
    kube::CustomResource, Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "RabbitmqCluster")]
#[kube(shortname = "rbmq", namespaced)]
pub struct RabbitmqClusterSpec {
    pub replicas: i32,
    #[serde(default = "default_persistence")]
    pub persistence: RabbitmqClusterPersistenceSpec,
    #[serde(rename = "rabbitmqConfig")]
    pub rabbitmq_config: Option<RabbitmqConfig>,
}

pub fn default_persistence() -> RabbitmqClusterPersistenceSpec {
    RabbitmqClusterPersistenceSpec {
        storage: default_storage(),
        storage_class_name: default_storage_class_name(),
    }
}

#[derive(Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema)]
pub struct RabbitmqConfig {
    #[serde(rename = "additionalConfig")]
    pub additional_config: Option<String>,
    #[serde(rename = "advancedConfig")]
    pub advanced_config: Option<String>,
    #[serde(rename = "envConfig")]
    pub env_config: Option<String>,
}

pub fn default_storage() -> k8s_openapi::apimachinery::pkg::api::resource::Quantity {
    k8s_openapi::apimachinery::pkg::api::resource::Quantity("10Gi".to_string())
}

pub fn default_storage_class_name() -> Option<String> {
    None
}

#[derive(Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema)]
pub struct RabbitmqClusterPersistenceSpec {
	#[serde(rename = "storageClassName", default = "default_storage_class_name")]
	pub storage_class_name: Option<String>,
	#[serde(default = "default_storage")]
    pub storage: k8s_openapi::apimachinery::pkg::api::resource::Quantity,
}

#[derive(
    kube::CustomResource, Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "FluentBit")]
#[kube(shortname = "fb", namespaced)]
pub struct FluentBitSpec {
    #[serde(rename = "fluentBitConfigName")]
    pub fluentbit_config_name: String,
    #[serde(default)]
    pub resources: k8s_openapi::api::core::v1::ResourceRequirements,
}

#[derive(
    kube::CustomResource, Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "FluentBitConfig")]
#[kube(shortname = "fbc", namespaced)]
pub struct FluentBitConfigSpec {
    #[serde(rename = "fluentBitConfig")]
    pub fluentbit_config: String,
    #[serde(rename = "parsersConfig")]
    pub parsers_config: String,
}
