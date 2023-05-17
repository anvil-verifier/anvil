use kube::CustomResource;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::vec;
use k8s_openapi::api::core::v1 as corev1;


#[derive(CustomResource, Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[kube(group = "anvil.dev", version = "v1", kind = "RabbitmqCluster")]
#[kube(shortname = "rm", namespaced)]
pub struct RabbitmqClusterSpec {
    pub replica: i32,
    #[serde(rename = "image", skip_serializing_if = "Option::is_none")]
    pub image: Option<String>,
    #[serde(rename = "image", skip_serializing_if = "Option::is_none")]
    pub image_pull_secrets: Option<vec::Vec<corev1::LocalObjectReference>>
}