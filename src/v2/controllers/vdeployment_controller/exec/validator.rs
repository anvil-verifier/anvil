use crate::kubernetes_api_objects::exec::dynamic::DynamicObject;
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;
use crate::vdeployment_controller::trusted::exec_types::{VDeployment, VDeploymentSpec};
use deps_hack::kube::core::{admission::AdmissionResponse, DynamicObject as KubeDynamicObject};
use std::error::Error;

pub fn validate_state(vdep: &VDeployment) -> Result<(), String> {
    // Call executable state validation
    if vdep.state_validation() {
        Ok(())
    } else {
        Err("Invalid VDeployment".to_string())
    }
}