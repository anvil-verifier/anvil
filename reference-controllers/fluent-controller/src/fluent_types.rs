use kube::CustomResource;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(CustomResource, Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[kube(group = "anvil.dev", version = "v1", kind = "FluentBit")]
#[kube(namespaced)]
pub struct FluentBitSpec {
    // The config field here is not actually used and the configuration data is hardcoded in the source code.
    // TODO(xudong): use the config field to pass configuration data and add more fields (features).
    pub config: String,
}
