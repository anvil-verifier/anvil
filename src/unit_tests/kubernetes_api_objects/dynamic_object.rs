// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::dynamic::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::vstd_ext::string_map::*;
use chrono::{DateTime, Utc};
use k8s_openapi::apimachinery::pkg::apis::meta::v1::Time;
use vstd::prelude::*;
use vstd::string::*;

#[test]
pub fn test_kube() {
    let kube_dynamic_object = kube::api::DynamicObject {
        metadata: kube::api::ObjectMeta {
            name: Some("name".to_string()),
            namespace: Some("namespace".to_string()),
            ..Default::default()
        },
        types: Some(kube::api::TypeMeta {
            api_version: "api_version".to_string(),
            kind: "kind".to_string(),
        }),
        data: serde_json::json!({
            "key": "value",
        }),
    };
    let dynamic_object = DynamicObject::from_kube(kube_dynamic_object.clone());
    assert_eq!(dynamic_object.into_kube(), kube_dynamic_object);
}

#[test]
pub fn test_metadata() {
    let dynamic_object = DynamicObject::from_kube(kube::api::DynamicObject {
        metadata: kube::api::ObjectMeta {
            name: Some("name".to_string()),
            namespace: Some("namespace".to_string()),
            ..Default::default()
        },
        types: Some(kube::api::TypeMeta {
            api_version: "api_version".to_string(),
            kind: "kind".to_string(),
        }),
        data: serde_json::json!({
            "key": "value",
        }),
    });
    assert_eq!(
        dynamic_object.metadata().into_kube(),
        kube::api::ObjectMeta {
            name: Some("name".to_string()),
            namespace: Some("namespace".to_string()),
            ..Default::default()
        }
    );
}

#[test]
pub fn test_clone() {
    let dynamic_object = DynamicObject::from_kube(kube::api::DynamicObject {
        metadata: kube::api::ObjectMeta {
            name: Some("name".to_string()),
            namespace: Some("namespace".to_string()),
            ..Default::default()
        },
        types: Some(kube::api::TypeMeta {
            api_version: "api_version".to_string(),
            kind: "kind".to_string(),
        }),
        data: serde_json::json!({
            "key": "value",
        }),
    });

    let cloned_dynamic_object = dynamic_object.clone();

    assert_eq!(
        dynamic_object.into_kube(),
        cloned_dynamic_object.into_kube()
    );
}

#[test]
pub fn test_fmt() {
    let dynamic_object = DynamicObject::from_kube(kube::api::DynamicObject {
        metadata: kube::api::ObjectMeta {
            name: Some("name".to_string()),
            namespace: Some("namespace".to_string()),
            ..Default::default()
        },
        types: Some(kube::api::TypeMeta {
            api_version: "api_version".to_string(),
            kind: "kind".to_string(),
        }),
        data: serde_json::json!({
            "key": "value",
        }),
    });
    assert_eq!(
        format!("{:?}", dynamic_object),
        format!("{:?}", dynamic_object.into_kube())
    );
}
