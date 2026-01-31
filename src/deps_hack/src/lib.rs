pub use anyhow;
pub use base64;
pub use chrono;
pub use futures;
pub use k8s_openapi;
pub use kube;
pub use kube_client;
pub use kube_core;
pub use kube_derive;
pub use proptest;
pub use rand;
pub use schemars;
pub use serde;
pub use serde_json;
pub use serde_yaml;
pub use thiserror;
pub use tokio;
pub use tracing;
pub use tracing_subscriber;
pub use warp;
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
#[kube(group = "anvil.dev", version = "v1", kind = "ZookeeperCluster")]
#[kube(shortname = "zk", namespaced)]
#[kube(status = "ZookeeperClusterStatus")]
pub struct ZookeeperClusterSpec {
    pub replicas: i32,
    pub image: String,
    pub ports: ZookeeperPorts,
    pub conf: ZookeeperConfig,
    pub persistence: ZookeeperPersistence,
    pub resources: Option<k8s_openapi::api::core::v1::ResourceRequirements>,
    pub affinity: Option<k8s_openapi::api::core::v1::Affinity>,
    pub tolerations: Option<Vec<k8s_openapi::api::core::v1::Toleration>>,
    #[serde(default, rename = "nodeSelector")]
    pub node_selector: std::collections::BTreeMap<String, String>,
    #[serde(default)]
    pub labels: std::collections::BTreeMap<String, String>,
    #[serde(default)]
    pub annotations: std::collections::BTreeMap<String, String>,
}

#[derive(Clone, Debug, Default, serde::Deserialize, serde::Serialize, schemars::JsonSchema)]
pub struct ZookeeperClusterStatus {
    pub ready_replicas: i32,
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
    pub storage_class_name: String,
}

#[derive(
    kube::CustomResource, Default, Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema,
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
    #[serde(
        rename = "podManagementPolicy",
        default = "default_pod_management_policy"
    )]
    pub pod_management_policy: String,
    #[serde(rename = "persistentVolumeClaimRetentionPolicy")]
    pub persistent_volume_claim_retention_policy:
        Option<k8s_openapi::api::apps::v1::StatefulSetPersistentVolumeClaimRetentionPolicy>,
}

pub fn default_pod_management_policy() -> String {
    "Parallel".to_string()
}

impl Default for RabbitmqCluster {
    fn default() -> Self {
        Self {
            metadata: k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta::default(),
            spec: RabbitmqClusterSpec::default(),
        }
    }
}

pub fn default_persistence() -> RabbitmqClusterPersistenceSpec {
    RabbitmqClusterPersistenceSpec {
        storage_class_name: default_storage_class_name(),
        storage: default_storage(),
    }
}

#[derive(Default, Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema)]
pub struct RabbitmqConfig {
    #[serde(rename = "additionalConfig")]
    pub additional_config: Option<String>,
    #[serde(rename = "advancedConfig")]
    pub advanced_config: Option<String>,
    #[serde(rename = "envConfig")]
    pub env_config: Option<String>,
}

pub fn default_storage_class_name() -> String {
    "standard".to_string()
}

pub fn default_storage() -> k8s_openapi::apimachinery::pkg::api::resource::Quantity {
    k8s_openapi::apimachinery::pkg::api::resource::Quantity("10Gi".to_string())
}

#[derive(Default, Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema)]
pub struct RabbitmqClusterPersistenceSpec {
    #[serde(rename = "storageClassName", default = "default_storage_class_name")]
    pub storage_class_name: String,
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
    pub image: String,
    pub args: Option<Vec<String>>,
    pub command: Option<Vec<String>>,
    #[serde(rename = "imagePullPolicy")]
    pub image_pull_policy: Option<String>,
    #[serde(rename = "imagePullSecrets")]
    pub image_pull_secrets: Option<Vec<k8s_openapi::api::core::v1::LocalObjectReference>>,
    #[serde(default)]
    pub resources: Option<k8s_openapi::api::core::v1::ResourceRequirements>,
    pub tolerations: Option<Vec<k8s_openapi::api::core::v1::Toleration>>,
    #[serde(default)]
    pub labels: std::collections::BTreeMap<String, String>,
    #[serde(default)]
    pub annotations: std::collections::BTreeMap<String, String>,
    #[serde(default, rename = "serviceAccountAnnotations")]
    pub service_account_annotations: std::collections::BTreeMap<String, String>,
    #[serde(default, rename = "serviceLabels")]
    pub service_labels: std::collections::BTreeMap<String, String>,
    #[serde(default, rename = "serviceSelector")]
    pub service_selector: Option<std::collections::BTreeMap<String, String>>,
    #[serde(default, rename = "serviceAnnotations")]
    pub service_annotations: std::collections::BTreeMap<String, String>,
    pub affinity: Option<k8s_openapi::api::core::v1::Affinity>,
    #[serde(default, rename = "disableLogVolumes")]
    pub disable_log_volumes: bool,
    #[serde(default, rename = "nodeSelector")]
    pub node_selector: std::collections::BTreeMap<String, String>,
    #[serde(rename = "runtimeClassName")]
    pub runtime_class_name: Option<String>,
    #[serde(rename = "dnsPolicy")]
    pub dns_policy: Option<String>,
    #[serde(rename = "priorityClassName")]
    pub priority_class_name: Option<String>,
    pub volumes: Option<Vec<k8s_openapi::api::core::v1::Volume>>,
    #[serde(rename = "volumeMounts")]
    pub volume_mounts: Option<Vec<k8s_openapi::api::core::v1::VolumeMount>>,
    #[serde(rename = "schedulerName")]
    pub scheduler_name: Option<String>,
    #[serde(rename = "metricsPort")]
    pub metrics_port: Option<i32>,
    #[serde(rename = "internalMountPropagation")]
    pub internal_mount_propagation: Option<String>,
    #[serde(rename = "positionDB")]
    pub position_db: Option<k8s_openapi::api::core::v1::HostPathVolumeSource>,
    #[serde(rename = "containerLogRealPath")]
    pub container_log_real_path: Option<String>,
    #[serde(rename = "securityContext")]
    pub security_context: Option<k8s_openapi::api::core::v1::PodSecurityContext>,
    #[serde(rename = "containerSecurityContext")]
    pub container_security_context: Option<k8s_openapi::api::core::v1::SecurityContext>,
    #[serde(rename = "hostNetwork")]
    pub host_network: Option<bool>,
    #[serde(rename = "envVars")]
    pub env_vars: Option<Vec<k8s_openapi::api::core::v1::EnvVar>>,
    #[serde(rename = "livenessProbe")]
    pub liveness_probe: Option<k8s_openapi::api::core::v1::Probe>,
    #[serde(rename = "readinessProbe")]
    pub readiness_probe: Option<k8s_openapi::api::core::v1::Probe>,
    #[serde(rename = "initContainers")]
    pub init_containers: Option<Vec<k8s_openapi::api::core::v1::Container>>,
    pub ports: Option<Vec<k8s_openapi::api::core::v1::ContainerPort>>,
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

#[derive(
    kube::CustomResource,
    Default,
    Debug,
    Clone,
    serde::Deserialize,
    serde::Serialize,
    schemars::JsonSchema,
    PartialEq,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "VReplicaSet")]
#[kube(shortname = "vrs", namespaced)]
pub struct VReplicaSetSpec {
    pub replicas: Option<i32>,
    pub selector: k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector,
    pub template: Option<k8s_openapi::api::core::v1::PodTemplateSpec>,
}

impl Default for VReplicaSet {
    fn default() -> Self {
        Self {
            metadata: k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta::default(),
            spec: VReplicaSetSpec::default(),
        }
    }
}

#[derive(
    kube::CustomResource,
    Default,
    Debug,
    Clone,
    serde::Deserialize,
    serde::Serialize,
    schemars::JsonSchema,
    PartialEq,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "VDeployment")]
#[kube(shortname = "vd", namespaced)]
pub struct VDeploymentSpec {
    pub replicas: Option<i32>,
    pub selector: k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector,
    pub template: k8s_openapi::api::core::v1::PodTemplateSpec,
    #[serde(rename = "minReadySeconds")]
    pub min_ready_seconds: Option<i32>,
    pub strategy: Option<k8s_openapi::api::apps::v1::DeploymentStrategy>,
    #[serde(rename = "revisionHistoryLimit")]
    pub revision_history_limit: Option<i32>,
    #[serde(rename = "progressDeadlineSeconds")]
    pub progress_deadline_seconds: Option<i32>,
    pub paused: Option<bool>,
}

impl Default for VDeployment {
    fn default() -> Self {
        Self {
            metadata: k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta::default(),
            spec: VDeploymentSpec::default(),
        }
    }
}

#[derive(
    kube::CustomResource,
    Default,
    Debug,
    Clone,
    serde::Deserialize,
    serde::Serialize,
    schemars::JsonSchema,
    PartialEq,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "VStatefulSet")]
#[kube(shortname = "vsts", namespaced)]
#[kube(status = "VStatefulSetStatus")]
pub struct VStatefulSetSpec {
    #[serde(rename = "serviceName")]
    pub service_name: String,
    pub selector: k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector,
    pub template: k8s_openapi::api::core::v1::PodTemplateSpec,
    pub replicas: Option<i32>,
    #[serde(rename = "updateStrategy")]
    pub update_strategy: Option<k8s_openapi::api::apps::v1::StatefulSetUpdateStrategy>,
    #[serde(rename = "podManagementPolicy")]
    pub pod_management_policy: Option<String>,
    #[serde(rename = "revisionHistoryLimit")]
    pub revision_history_limit: Option<i32>,
    #[serde(rename = "volumeClaimTemplates")]
    pub volume_claim_templates: Option<Vec<k8s_openapi::api::core::v1::PersistentVolumeClaim>>,
    #[serde(rename = "minReadySeconds")]
    pub min_ready_seconds: Option<i32>,
    #[serde(rename = "persistentVolumeClaimRetentionPolicy")]
    pub persistent_volume_claim_retention_policy:
        Option<k8s_openapi::api::apps::v1::StatefulSetPersistentVolumeClaimRetentionPolicy>,
    pub ordinals: Option<k8s_openapi::api::apps::v1::StatefulSetOrdinals>,
}

#[derive(
    Clone, Debug, Default, serde::Deserialize, serde::Serialize, schemars::JsonSchema, PartialEq,
)]
pub struct VStatefulSetStatus {
    pub replicas: i32,
    #[serde(rename = "readyReplicas")]
    pub ready_replicas: Option<i32>,
    #[serde(rename = "currentReplicas")]
    pub current_replicas: Option<i32>,
    #[serde(rename = "updatedReplicas")]
    pub updated_replicas: Option<i32>,
    #[serde(rename = "availableReplicas")]
    pub available_replicas: Option<i32>,
    #[serde(rename = "collisionCount")]
    pub collision_count: Option<i32>,
    pub conditions: Option<Vec<k8s_openapi::api::apps::v1::StatefulSetCondition>>,
    #[serde(rename = "currentRevision")]
    pub current_revision: Option<String>,
    #[serde(rename = "updateRevision")]
    pub update_revision: Option<String>,
    #[serde(rename = "observedGeneration")]
    pub observed_generation: Option<i64>,
}

impl Default for VStatefulSet {
    fn default() -> Self {
        Self {
            metadata: k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta::default(),
            spec: VStatefulSetSpec::default(),
            status: None,
        }
    }
}

impl VStatefulSetSpec {
    // This is a workaround to allows us to
    // (1) create VStatefulSet through VStatefulSetSpec using macros from k8s_openapi, and
    // (2) reuse the wrapper type of k8s_openapi::api::apps::v1::StatefulSetSpec for VStatefulSet
    // instead of creating a new wrapper type for VStatefulSetSpec.
    pub fn to_native(&self) -> k8s_openapi::api::apps::v1::StatefulSetSpec {
        k8s_openapi::api::apps::v1::StatefulSetSpec {
            service_name: self.service_name.clone(),
            selector: self.selector.clone(),
            template: self.template.clone(),
            replicas: self.replicas.clone(),
            update_strategy: self.update_strategy.clone(),
            pod_management_policy: self.pod_management_policy.clone(),
            revision_history_limit: self.revision_history_limit.clone(),
            volume_claim_templates: self.volume_claim_templates.clone(),
            min_ready_seconds: self.min_ready_seconds.clone(),
            persistent_volume_claim_retention_policy: self
                .persistent_volume_claim_retention_policy
                .clone(),
            ordinals: self.ordinals.clone(),
        }
    }
}
