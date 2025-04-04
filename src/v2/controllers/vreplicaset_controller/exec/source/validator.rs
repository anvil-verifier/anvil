use kube::core::{admission::AdmissionResponse, DynamicObject};
use std::error::Error;

//import VReplicaSet from exec.types.rs
use crate::vreplicaset_controller::trusted::exec_types::VReplicaSet;

/// main validation
pub fn validate_state(
    res: AdmissionResponse,
    obj: &DynamicObject,
) -> Result<AdmissionResponse, Box<dyn Error>> {
    // extract object into VReplicaSet
    let vrs_result = VReplicaSet::unmarshal(obj.clone());
    if vrs_result.is_err() {
        return Err("Can't extract into VReplicaSet".into());
    }
    let vrs = vrs_result.unwrap();
    
    let spec = vrs.spec();
    
    // three different validation
    validate_replicas(&spec)?;
    validate_selector(&spec)?;
    validate_template(&spec)?;
    
    Ok(res)
}

/// validate replicas in spec
pub fn validate_replicas(spec: &crate::vreplicaset_controller::trusted::exec_types::VReplicaSetSpec) -> Result<(), Box<dyn Error>> {
    if let Some(replicas) = spec.replicas() {
        if replicas < 0 {
            return Err("Invalid 'spec.replicas': must be non-negative".into());
        }
    }
    Ok(())
}

/// validate sleector in spec
pub fn validate_selector(spec: &crate::vreplicaset_controller::trusted::exec_types::VReplicaSetSpec) -> Result<(), Box<dyn Error>> {
    let selector = spec.selector();
    let match_labels = selector.match_labels();
    if match_labels.is_none() || match_labels.as_ref().unwrap().len() == 0 {
        return Err("Invalid 'spec.selector.matchLabels': must not be empty".into());
    }
    Ok(())
}

/// validate template in spec
pub fn validate_template(spec: &crate::vreplicaset_controller::trusted::exec_types::VReplicaSetSpec) -> Result<(), Box<dyn Error>> {
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
    
    for (key, value) in match_labels.iter() {
        if let Some(template_value) = tmpl_labels.get(key) {
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
    
    Ok(())
}