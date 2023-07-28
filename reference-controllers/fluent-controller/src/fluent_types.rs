use kube::CustomResource;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(CustomResource, Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[kube(group = "anvil.dev", version = "v1", kind = "FluentBit")]
#[kube(namespaced)]
pub struct FluentBitSpec {
    pub config: String,
}
