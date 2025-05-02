use crate::kubernetes_api_objects::exec::dynamic::DynamicObject;
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;
use crate::vstatefulset_controller::trusted::exec_types::{VStatefulSet, VStatefulSetSpec};
use deps_hack::kube::core::{admission::AdmissionResponse, DynamicObject as KubeDynamicObject};
use std::error::Error;

pub fn validate_state(vss: &VStatefulSet) -> Result<(), String> {
    // Call executable state validation
    if vss.state_validation() {
        Ok(())
    } else {
        Err("Invalid VStatefulSet".to_string())
    }
}