use kube::Client;
use kube::CustomResource;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use thiserror::Error;

#[derive(CustomResource, Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[kube(group = "anvil.dev", version = "v1", kind = "FluentBit")]
#[kube(namespaced)]
pub struct FluentBitSpec {
    #[serde(rename = "fluentBitConfigName")]
    pub fluent_bit_config_name: String,
}

#[derive(CustomResource, Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[kube(group = "anvil.dev", version = "v1", kind = "FluentBitConfig")]
#[kube(namespaced)]
pub struct FluentBitConfigSpec {
    pub config: String,
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("Failed to get CR: {0}")]
    CRGetFailed(#[source] kube::Error),
    #[error("Failed to get Secret: {0}")]
    SecretGetFailed(#[source] kube::Error),
    #[error("Failed to reconcile Role: {0}")]
    ReconcileRoleFailed(#[source] kube::Error),
    #[error("Failed to reconcile ServiceAccount: {0}")]
    ReconcileServiceAccountFailed(#[source] kube::Error),
    #[error("Failed to reconcile RoleBinding: {0}")]
    ReconcileRoleBindingFailed(#[source] kube::Error),
    #[error("Failed to reconcile Secret: {0}")]
    ReconcileSecretFailed(#[source] kube::Error),
    #[error("Failed to reconcile DaemonSet: {0}")]
    ReconcileDaemonSetFailed(#[source] kube::Error),
    #[error("MissingObjectKey: {0}")]
    MissingObjectKey(&'static str),
}

pub struct Data {
    pub client: Client,
}
