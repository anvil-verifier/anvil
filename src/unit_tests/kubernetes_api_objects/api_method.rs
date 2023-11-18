// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::api_method::*;
use crate::kubernetes_api_objects::exec::api_resource::*;
use crate::kubernetes_api_objects::exec::dynamic::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::vstd_ext::string_map::*;
use deps_hack::chrono::{DateTime, Utc};
use deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::Time;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for api method
#[test]
#[verifier(external)]
pub fn test_getrequest_key() {
    let api_method = KubeGetRequest {
        api_resource: ApiResource::from_kube(
            deps_hack::kube::api::ApiResource {
                group: "group".to_string(),
                version: "version".to_string(),
                kind: "kind".to_string(),
                api_version: "api_version".to_string(),
                plural: "plural".to_string(),
            },
        ),
        name: new_strlit("name").to_string(),
        namespace: new_strlit("namespace").to_string(),
    };
    assert_eq!(
        api_method.key(),
        "kind/namespace/name"
    );
}

#[test]
#[verifier(external)]
pub fn test_listrequest_key() {
    let api_method = KubeListRequest {
        api_resource: ApiResource::from_kube(
            deps_hack::kube::api::ApiResource {
                group: "group".to_string(),
                version: "version".to_string(),
                kind: "kind".to_string(),
                api_version: "api_version".to_string(),
                plural: "plural".to_string(),
            },
        ),
        namespace: new_strlit("namespace").to_string(),
    };
    assert_eq!(
        api_method.key(),
        "kind/namespace"
    );
}

#[test]
#[verifier(external)]
pub fn test_createquest_key() {
    let api_method = KubeCreateRequest {
        api_resource: ApiResource::from_kube(
            deps_hack::kube::api::ApiResource {
                group: "group".to_string(),
                version: "version".to_string(),
                kind: "kind".to_string(),
                api_version: "api_version".to_string(),
                plural: "plural".to_string(),
            },
        ),
        namespace: new_strlit("namespace").to_string(),
        obj:  DynamicObject::from_kube(
                deps_hack::kube::api::DynamicObject {
                metadata: deps_hack::kube::api::ObjectMeta {
                    name: Some("dyn_name".to_string()),
                    namespace: Some("namespace".to_string()),
                    ..Default::default()
                },
                types: Some(deps_hack::kube::api::TypeMeta {
                    api_version: "api_version".to_string(),
                    kind: "kind".to_string(),
                }),
                data: deps_hack::serde_json::json!({
                    "key": "value",
                }),
            },
        )
    };
    assert_eq!(
        api_method.key(),
        "kind/namespace/dyn_name"
    );
}

#[test]
#[verifier(external)]
pub fn test_deleterequest_key() {
    let api_method = KubeDeleteRequest {
        api_resource: ApiResource::from_kube(
            deps_hack::kube::api::ApiResource {
                group: "group".to_string(),
                version: "version".to_string(),
                kind: "kind".to_string(),
                api_version: "api_version".to_string(),
                plural: "plural".to_string(),
            },
        ),
        name: new_strlit("name").to_string(),
        namespace: new_strlit("namespace").to_string(),
    };
    assert_eq!(
        api_method.key(),
        "kind/namespace/name"
    );
}

#[test]
#[verifier(external)]
pub fn test_updaterequest_key() {
    let api_method = KubeUpdateRequest {
        api_resource: ApiResource::from_kube(
            deps_hack::kube::api::ApiResource {
                group: "group".to_string(),
                version: "version".to_string(),
                kind: "kind".to_string(),
                api_version: "api_version".to_string(),
                plural: "plural".to_string(),
            },
        ),
        name: new_strlit("name").to_string(),
        namespace: new_strlit("namespace").to_string(),
        obj:  DynamicObject::from_kube(
                deps_hack::kube::api::DynamicObject {
                metadata: deps_hack::kube::api::ObjectMeta {
                    name: Some("dyn_name".to_string()),
                    namespace: Some("namespace".to_string()),
                    ..Default::default()
                },
                types: Some(deps_hack::kube::api::TypeMeta {
                    api_version: "api_version".to_string(),
                    kind: "kind".to_string(),
                }),
                data: deps_hack::serde_json::json!({
                    "key": "value",
                }),
            },
        )
    };
    assert_eq!(
        api_method.key(),
        "kind/namespace/name"
    );
}

#[test]
#[verifier(external)]
pub fn test_updatestatusrequest_key() {
    let api_method = KubeUpdateStatusRequest {
        api_resource: ApiResource::from_kube(
            deps_hack::kube::api::ApiResource {
                group: "group".to_string(),
                version: "version".to_string(),
                kind: "kind".to_string(),
                api_version: "api_version".to_string(),
                plural: "plural".to_string(),
            },
        ),
        name: new_strlit("name").to_string(),
        namespace: new_strlit("namespace").to_string(),
        obj:  DynamicObject::from_kube(
                deps_hack::kube::api::DynamicObject {
                metadata: deps_hack::kube::api::ObjectMeta {
                    name: Some("dyn_name".to_string()),
                    namespace: Some("namespace".to_string()),
                    ..Default::default()
                },
                types: Some(deps_hack::kube::api::TypeMeta {
                    api_version: "api_version".to_string(),
                    kind: "kind".to_string(),
                }),
                data: deps_hack::serde_json::json!({
                    "key": "value",
                }),
            },
        )
    };
    assert_eq!(
        api_method.key(),
        "kind/namespace/name"
    );
}


}
