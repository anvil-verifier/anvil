// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

use kube::CustomResource;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

// This is our CRD: it contains command to create/delete/update configmaps
// and the content of the configmaps
#[derive(CustomResource, Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[kube(group = "nullable.se", version = "v1", kind = "ConfigMapGenerator")]
#[kube(shortname = "cmg", namespaced)]
pub struct ConfigMapGeneratorSpec {
    pub content: String, // The configmap is supposed to contain the content; we can ignore it for now
    pub command: String, // The command decides whether to create the configmap; we can ignore it for now
}
