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
    #[error("ShimLayerError: {0}")]
    ShimLayerError(String),
    #[error("ReconcileCoreError")]
    ReconcileCoreError,
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
    pub persistence: ZookeeperPersistence,
    pub resources: Option<k8s_openapi::api::core::v1::ResourceRequirements>,
    pub affinity: Option<k8s_openapi::api::core::v1::Affinity>,
    pub tolerations: Option<Vec<k8s_openapi::api::core::v1::Toleration>>,
    #[serde(default)]
    pub node_selector: std::collections::BTreeMap<String, String>,
    #[serde(default)]
    pub labels: std::collections::BTreeMap<String, String>,
    #[serde(default)]
    pub annotations: std::collections::BTreeMap<String, String>,
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

#[derive(Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema)]
pub struct ZookeeperPersistence {
    pub enabled: bool,
    #[serde(rename = "storageSize")]
    pub storage_size: k8s_openapi::apimachinery::pkg::api::resource::Quantity,
    #[serde(rename = "storageClassName")]
    pub storage_class_name: Option<String>,
}

#[derive(
    kube::CustomResource, Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "RabbitmqCluster")]
#[kube(shortname = "rbmq", namespaced)]
pub struct RabbitmqClusterSpec {
    pub replicas: i32,
    /// Image is the name of the RabbitMQ docker image to use for RabbitMQ nodes in the RabbitmqCluster.
    pub image: String,
    #[serde(default = "default_persistence")]
    pub persistence: RabbitmqClusterPersistenceSpec,
    #[serde(rename = "rabbitmqConfig")]
    pub rabbitmq_config: Option<RabbitmqConfig>,
    pub affinity: Option<k8s_openapi::api::core::v1::Affinity>,
    pub tolerations: Option<Vec<k8s_openapi::api::core::v1::Toleration>>,
    #[serde(default)]
    pub labels: std::collections::BTreeMap<String, String>,
    #[serde(default)]
    pub annotations: std::collections::BTreeMap<String, String>,
    pub resources: Option<k8s_openapi::api::core::v1::ResourceRequirements>,
    /// podManagementPolicy controls how pods are created during initial scale up,
    /// when replacing pods on nodes, or when scaling down. The default policy is
    /// `OrderedReady`, where pods are created in increasing order (pod-0, then
    /// pod-1, etc) and the controller will wait until each pod is ready before
    /// continuing. When scaling down, the pods are removed in the opposite order.
    /// The alternative policy is `Parallel` which will create pods in parallel
    /// to match the desired scale without waiting, and on scale down will delete
    /// all pods at once.
    #[serde(rename = "podManagementPolicy")]
    pub pod_management_policy: Option<String>,
    #[serde(rename = "persistentVolumeClaimRetentionPolicy")]
    pub persistent_volume_claim_retention_policy:
        Option<k8s_openapi::api::apps::v1::StatefulSetPersistentVolumeClaimRetentionPolicy>,
}

pub fn default_persistence() -> RabbitmqClusterPersistenceSpec {
    RabbitmqClusterPersistenceSpec {
        storage: default_storage(),
        storage_class_name: None,
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

#[derive(Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema)]
pub struct RabbitmqClusterPersistenceSpec {
    #[serde(rename = "storageClassName", default)]
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
    pub resources: Option<k8s_openapi::api::core::v1::ResourceRequirements>,
    pub tolerations: Option<Vec<k8s_openapi::api::core::v1::Toleration>>,
    #[serde(default)]
    pub labels: std::collections::BTreeMap<String, String>,
    #[serde(default)]
    pub annotations: std::collections::BTreeMap<String, String>,
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
