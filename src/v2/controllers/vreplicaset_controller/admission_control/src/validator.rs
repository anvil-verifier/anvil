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
