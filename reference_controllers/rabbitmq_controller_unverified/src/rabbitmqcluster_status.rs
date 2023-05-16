use kube::CustomResource;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::vec;
use k8s_openapi::api::core::v1 as corev1;

#[derive(CustomResource, Debug, Clone, Deserialize, Serialize, JsonSchema)]
pub struct RabbitmqClusterStatus {
}

struct RabbitmqClusterCondition {
    type : String,
    status : corev1.ConditionStatus,
}