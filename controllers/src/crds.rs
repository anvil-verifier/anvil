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
