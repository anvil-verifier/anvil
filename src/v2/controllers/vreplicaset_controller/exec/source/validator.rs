use deps_hack::kube::core::{admission::AdmissionResponse, DynamicObject as KubeDynamicObject};
use std::error::Error;
use crate::vreplicaset_controller::trusted::exec_types::{VReplicaSet, VReplicaSetSpec};
use crate::kubernetes_api_objects::exec::dynamic::DynamicObject;
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;

pub fn validate_state(
    res: AdmissionResponse,
    obj: &KubeDynamicObject,
) -> Result<AdmissionResponse, Box<dyn Error>> {
    // Convert from KubeDynamicObject to DynamicObject
    // We assume there's a method to convert from KubeDynamicObject to local DynamicObject
    // According to the unmarshal function in exec_types.rs, it expects a DynamicObject type
    let local_obj = DynamicObject::from_kube(obj.clone());
    
    // Use unmarshal function to convert DynamicObject to VReplicaSet
    let vrs_result = VReplicaSet::unmarshal(local_obj);
    if vrs_result.is_err() {
        return Err("Failed to unmarshal VReplicaSet".into());
    }
    
    // Get the VReplicaSet instance and its spec
    let vrs = vrs_result.unwrap();

    // Call executable state validation
    let state_valid = vrs.state_validation();

    if state_valid == false {
        return Err("Invalid VReplicaset".into())
    }

    Ok(res)
}
