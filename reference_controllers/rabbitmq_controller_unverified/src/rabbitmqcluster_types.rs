use kube::CustomResource;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::vec;

#[derive(CustomResource, Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[kube(group = "anvil.dev", version = "v1", kind = "RabbitmqCluster")]
#[kube(shortname = "rm", namespaced)]
pub struct RabbitmqClusterSpec {
    pub replica: i32,
    pub image: String,
    pub image_pull_secrets: Option<vec::Vec<String>>
}