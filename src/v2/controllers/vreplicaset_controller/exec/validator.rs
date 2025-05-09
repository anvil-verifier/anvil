#![allow(unused_imports)]

use crate::kubernetes_api_objects::exec::dynamic::DynamicObject;
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;
use crate::vreplicaset_controller::trusted::exec_types::{VReplicaSet, VReplicaSetSpec};
use deps_hack::kube::core::{admission::AdmissionResponse, DynamicObject as KubeDynamicObject};
use std::error::Error;

pub fn validate_state(vrs: &VReplicaSet) -> Result<(), String> {
    // Call executable state validation
    if vrs.state_validation() {
        Ok(())
    } else {
        Err("Invalid VReplicaset".to_string())
    }
}
