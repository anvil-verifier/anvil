use crate::kubernetes_api_objects::exec::dynamic::DynamicObject;
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;
use crate::kubernetes_api_objects::spec::resource::ResourceView;
use crate::v_replica_set_controller::trusted::exec_types::{VReplicaSet, VReplicaSetSpec};
use crate::v_replica_set_controller::trusted::spec_types::VReplicaSetView;
use deps_hack::kube::core::{admission::AdmissionResponse, DynamicObject as KubeDynamicObject};
use std::error::Error;

use vstd::prelude::*;

verus !{

// #[verifier(external_body)]
// pub fn validate_state(
//     res: AdmissionResponse,
//     obj: &KubeDynamicObject,
// ) -> Result<AdmissionResponse, String> {
//     // Convert from KubeDynamicObject to DynamicObject
//     // We assume there's a method to convert from KubeDynamicObject to local DynamicObject
//     // According to the unmarshal function in exec_types.rs, it expects a DynamicObject type
//     let local_obj = DynamicObject::from_kube(obj.clone());

//     // Use unmarshal function to convert DynamicObject to VReplicaSet
//     let vrs_result = VReplicaSet::unmarshal(local_obj);
//     if vrs_result.is_err() {
//         return Err("Failed to unmarshal VReplicaSet".to_string());
//     }

//     // Get the VReplicaSet instance and its spec
//     let vrs = vrs_result.unwrap();

//     // Validation part remains unchanged
//     validate_replicas(&vrs)?;
//     Ok(res)
// }

/// Validate that the replicas field in spec exists and is non-negative
pub fn validate_replicas(vrs: &VReplicaSet) -> (res: Result<(), String>)
    ensures
        match res {
            Ok(_) => vrs@.state_validation() == true,
            Err(_) => vrs@.state_validation() == false,
        }
{
    if let Some(replicas) = vrs.spec().replicas() {
        if replicas < 0 {
            return Err("Invalid 'spec.replicas': must be non-negative".to_string());
        }
    }
    Ok(())
}

}