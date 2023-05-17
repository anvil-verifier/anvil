use kube::CustomResource;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::vec;
use k8s_openapi::api::core::v1 as corev1;


pub struct RabbitmqClusterStatus {
}

pub struct RabbitmqClusterCondition {
    t_ype : String,
    status : String,
}