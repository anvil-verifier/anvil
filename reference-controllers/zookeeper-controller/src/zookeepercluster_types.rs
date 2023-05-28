use kube::CustomResource;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::vec;

#[derive(CustomResource, Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[kube(group = "anvil.dev", version = "v1", kind = "ZookeeperCluster")]
#[kube(shortname = "zk", namespaced)]
pub struct ZookeeperClusterSpec {
    pub replica: i32,
}
