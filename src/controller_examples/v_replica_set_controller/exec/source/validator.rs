use deps_hack::kube::core::{admission::AdmissionResponse, DynamicObject as KubeDynamicObject};
use std::error::Error;
use crate::v_replica_set_controller::trusted::exec_types::{VReplicaSet, VReplicaSetSpec};
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
    let spec = vrs.spec();
    
    // Validation part remains unchanged
    validate_replicas(&spec)?;
    validate_selector(&spec)?;
    validate_template(&spec)?;
    Ok(res)
}

/// Validate that the replicas field in spec exists and is non-negative
pub fn validate_replicas(spec: &VReplicaSetSpec) -> Result<(), Box<dyn Error>> {
    if let Some(replicas) = spec.replicas() {
        if replicas < 0 {
            return Err("Invalid 'spec.replicas': must be non-negative".into());
        }
    }
    Ok(())
}

/// Validate that the selector's matchLabels field in spec exists and is not empty
pub fn validate_selector(spec: &VReplicaSetSpec) -> Result<(), Box<dyn Error>> {
    let selector = spec.selector();
    let match_labels = selector.match_labels();
    if match_labels.is_none() || match_labels.as_ref().unwrap().len() == 0 {
        return Err("Invalid 'spec.selector.matchLabels': must not be empty".into());
    }
    Ok(())
}

/// Validate that the required fields in template exist, and that template labels match selector.matchLabels
pub fn validate_template(spec: &VReplicaSetSpec) -> Result<(), Box<dyn Error>> {
    let template_opt = spec.template();
    if template_opt.is_none() {
        return Err("Missing 'spec.template' field".into());
    }
    
    let template = template_opt.unwrap();
    if template.metadata().is_none() {
        return Err("Missing 'spec.template.metadata' field".into());
    }
    
    if template.spec().is_none() {
        return Err("Missing 'spec.template.spec' field".into());
    }
    
    let selector = spec.selector();
    let match_labels = selector.match_labels().ok_or("Missing 'spec.selector.matchLabels'")?;
    let tmpl_meta_opt = template.metadata();
    let tmpl_labels_opt = tmpl_meta_opt.unwrap().labels();
    
    if tmpl_labels_opt.is_none() {
        return Err("Invalid 'spec.template.metadata.labels': must be an object".into());
    }
    
    let tmpl_labels = tmpl_labels_opt.unwrap();
    
    // From the error messages, StringMap doesn't have an iter() method and doesn't support indexing
    // We need to use the get method, and we need to provide a reference to String
    
    // Get all keys from match_labels
    // Assuming StringMap has a keys() method
    for key in match_labels.keys() {
        // Use &key as a reference passed to the get method
        if let Some(value) = match_labels.get(&key) {
            if let Some(template_value) = tmpl_labels.get(&key) {
                if template_value != value {
                    return Err(format!(
                        "Selector matchLabel '{}' value mismatch in template labels",
                        key
                    ).into());
                }
            } else {
                return Err(format!(
                    "Selector matchLabel '{}' not found in template labels",
                    key
                ).into());
            }
        }
    }
    
    Ok(())
}