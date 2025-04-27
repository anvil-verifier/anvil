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

    // dont currently exist in the crd, but should still pass since they are optional
    validate_strategy(spec)?;
    validate_min_ready_seconds(spec)?;
    validate_progress_deadline_seconds(spec)?;

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

fn validate_strategy(spec: &serde_json::Value) -> Result<(), Box<dyn Error>> {
    if let Some(strategy) = spec.get("strategy") {
        
        if let Some(strategy_type) = strategy.get("type") {
            let type_str = strategy_type.as_str()
                .ok_or("Invalid 'spec.strategy.type': must be a string")?;
            
            // should be Recreate or RollingUpdate
            if type_str != "Recreate" && type_str != "RollingUpdate" {
                return Err(format!(
                    "Invalid 'spec.strategy.type': '{}' is not a valid strategy type. Must be 'Recreate' or 'RollingUpdate'",
                    type_str
                ).into());
            }

            // if recreate, should not have rollingUpdate
            if type_str == "Recreate" {
                if strategy.get("rollingUpdate").is_some() {
                    return Err("Invalid: 'spec.strategy.rollingUpdate' should not be present when 'type' is 'Recreate'".into());
                }
            }
        }

        if let Some(rolling_update) = strategy.get("rollingUpdate") {
            // these cannot both be 0
            let max_surge = rolling_update.get("maxSurge");
            let max_unavailable = rolling_update.get("maxUnavailable");
            
            let max_surge_zero = max_surge
                .and_then(|v| v.as_i64())
                .map_or(false, |v| v == 0);
            
            let max_unavailable_zero = max_unavailable
                .and_then(|v| v.as_i64())
                .map_or(false, |v| v == 0);
            
            if max_surge_zero && max_unavailable_zero {
                return Err("Invalid: 'maxSurge' and 'maxUnavailable' cannot both be 0".into());
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

fn validate_progress_deadline_seconds(spec: &serde_json::Value) -> Result<(), Box<dyn Error>> {
    if let Some(progress_deadline) = spec.get("progressDeadlineSeconds") {
        if progress_deadline.as_i64().map_or(true, |s| s < 0) {
            return Err("Invalid 'spec.progressDeadlineSeconds': must be non-negative".into());
        }
    }
    Ok(())
}

