use kube::core::{admission::AdmissionResponse, DynamicObject};
use std::error::Error;

/// Main validation function
pub fn validate_state(
    res: AdmissionResponse,
    obj: &DynamicObject,
) -> Result<AdmissionResponse, Box<dyn Error>> {
    let spec = obj
        .data
        .get("spec")
        .ok_or("Missing 'spec' field in the object")?;

    validate_replicas(spec)?;
    validate_selector(spec)?;
    validate_template(spec)?;
    validate_update_strategy(spec)?;
    validate_pod_management_policy(spec)?;
    validate_volume_claim_templates(spec)?;
    validate_min_ready_seconds(spec)?;
    validate_persistent_volume_claim_retention_policy(spec)?;
    validate_ordinals(spec)?;

    Ok(res)
}

fn validate_replicas(spec: &serde_json::Value) -> Result<(), Box<dyn Error>> {
    if let Some(replicas) = spec.get("replicas") {
        if replicas.as_i64().map_or(true, |r| r < 0) {
            return Err("Invalid 'spec.replicas': must be non-negative".into());
        }
    }
    Ok(())
}

fn validate_selector(spec: &serde_json::Value) -> Result<(), Box<dyn Error>> {
    let selector = spec
        .get("selector")
        .ok_or("Missing 'spec.selector' field")?;
    let match_labels = selector
        .get("matchLabels")
        .ok_or("Missing 'spec.selector.matchLabels' field")?;
    let match_labels = match_labels
        .as_object()
        .ok_or("Invalid 'spec.selector.matchLabels': must be an object")?;

    if match_labels.is_empty() {
        return Err("Invalid 'spec.selector.matchLabels': must not be empty".into());
    }

    Ok(())
}

fn validate_template(spec: &serde_json::Value) -> Result<(), Box<dyn Error>> {
    let selector = spec.get("selector").unwrap().get("matchLabels").unwrap();
    let match_labels = selector.as_object().unwrap();

    let template = spec.get("template").ok_or("Missing 'spec.template' field")?;
    let metadata = template
        .get("metadata")
        .ok_or("Missing 'spec.template.metadata' field")?;
    let template_labels = metadata
        .get("labels")
        .and_then(|l| l.as_object())
        .ok_or("Invalid 'spec.template.metadata.labels': must be an object")?;

    for (key, value) in match_labels {
        match template_labels.get(key) {
            Some(template_value) if template_value == value => continue,
            _ => {
                return Err(format!(
                    "Selector matchLabel '{}' not found in template labels or value doesn't match",
                    key
                )
                .into())
            }
        }
    }

    template.get("spec")
        .ok_or("Missing 'spec.template.spec' field")?;

    Ok(())
}

fn validate_update_strategy(spec: &serde_json::Value) -> Result<(), Box<dyn Error>> {
    if let Some(update_strategy) = spec.get("updateStrategy") {
        
        if let Some(strategy_type) = update_strategy.get("type") {
            let type_str = strategy_type.as_str()
                .ok_or("Invalid 'spec.updateStrategy.type': must be a string")?;
            
            // should be RollingUpdate or OnDelete
            if type_str != "RollingUpdate" && type_str != "OnDelete" {
                return Err(format!(
                    "Invalid 'spec.updateStrategy.type': '{}' is not a valid strategy type. Must be 'RollingUpdate' or 'OnDelete'",
                    type_str
                ).into());
            }

            // if OnDelete, should not have rollingUpdate
            if type_str == "OnDelete" {
                if update_strategy.get("rollingUpdate").is_some() {
                    return Err("Invalid: 'spec.updateStrategy.rollingUpdate' should not be present when 'type' is 'OnDelete'".into());
                }
            }
        }

        if let Some(rolling_update) = update_strategy.get("rollingUpdate") {
            // partition is non-negative
            if let Some(partition) = rolling_update.get("partition") {
                if partition.as_i64().map_or(true, |p| p < 0) {
                    return Err("Invalid 'spec.updateStrategy.rollingUpdate.partition': must be non-negative".into());
                }
            }
            
            // maxUnavailable is positive
            if let Some(max_unavailable) = rolling_update.get("maxUnavailable") {
                if max_unavailable.as_i64().map_or(true, |p| p <= 0) {
                    return Err("Invalid 'spec.updateStrategy.rollingUpdate.maxUnavailable': must be non-negative".into());
                }
            }
        }
    }

    Ok(())
}

fn validate_pod_management_policy(spec: &serde_json::Value) -> Result<(), Box<dyn Error>> {
    if let Some(policy) = spec.get("podManagementPolicy") {
        let policy_str = policy.as_str()
            .ok_or("Invalid 'spec.podManagementPolicy': must be a string")?;
        
        if policy_str != "OrderedReady" && policy_str != "Parallel" {
            return Err(format!(
                "Invalid 'spec.podManagementPolicy': '{}' is not a valid policy. Must be 'OrderedReady' or 'Parallel'",
                policy_str
            ).into());
        }
    }
    Ok(())
}

fn validate_volume_claim_templates(spec: &serde_json::Value) -> Result<(), Box<dyn Error>> {
    if let Some(templates) = spec.get("volumeClaimTemplates") {
        if !templates.is_array() {
            return Err("Invalid 'spec.volumeClaimTemplates': must be an array".into());
        }
        
        let templates_array = templates.as_array().unwrap();
        
        if templates_array.len() >= 100 {
            return Err("Invalid 'spec.volumeClaimTemplates': too many templates (limit is 99)".into());
        }
        
        for (i, template) in templates_array.iter().enumerate() {
            if !template.get("spec").is_some() {
                return Err(format!(
                    "Invalid 'spec.volumeClaimTemplates[{}]': missing 'spec' field",
                    i
                ).into());
            }
        }
    }
    Ok(())
}

fn validate_min_ready_seconds(spec: &serde_json::Value) -> Result<(), Box<dyn Error>> {
    if let Some(min_ready_seconds) = spec.get("minReadySeconds") {
        if min_ready_seconds.as_i64().map_or(true, |s| s < 0) {
            return Err("Invalid 'spec.minReadySeconds': must be non-negative".into());
        }
    }
    Ok(())
}

fn validate_persistent_volume_claim_retention_policy(spec: &serde_json::Value) -> Result<(), Box<dyn Error>> {
    if let Some(policy) = spec.get("persistentVolumeClaimRetentionPolicy") {

        if let Some(when_deleted) = policy.get("whenDeleted") {
            let when_deleted_str = when_deleted.as_str()
                .ok_or("Invalid 'spec.persistentVolumeClaimRetentionPolicy.whenDeleted': must be a string")?;
            
            if when_deleted_str != "Retain" && when_deleted_str != "Delete" {
                return Err(format!(
                    "Invalid 'spec.persistentVolumeClaimRetentionPolicy.whenDeleted': '{}' is not valid. Must be 'Retain' or 'Delete'",
                    when_deleted_str
                ).into());
            }
        }
        
        if let Some(when_scaled) = policy.get("whenScaled") {
            let when_scaled_str = when_scaled.as_str()
                .ok_or("Invalid 'spec.persistentVolumeClaimRetentionPolicy.whenScaled': must be a string")?;
            
            if when_scaled_str != "Retain" && when_scaled_str != "Delete" {
                return Err(format!(
                    "Invalid 'spec.persistentVolumeClaimRetentionPolicy.whenScaled': '{}' is not valid. Must be 'Retain' or 'Delete'",
                    when_scaled_str
                ).into());
            }
        }
    }
    Ok(())
}

fn validate_ordinals(spec: &serde_json::Value) -> Result<(), Box<dyn Error>> {
    if let Some(ordinals) = spec.get("ordinals") {
        if let Some(start) = ordinals.get("start") {
            if start.as_i64().map_or(true, |s| s < 0) {
                return Err("Invalid 'spec.ordinals.start': must be non-negative".into());
            }
        }
    }
    Ok(())
}
