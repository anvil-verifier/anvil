// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::api_resource::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::vstd_ext::string_map::*;
use deps_hack::chrono::{DateTime, Utc};
use deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::Time;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for api resource
#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_api_resource =
        deps_hack::kube::api::ApiResource  {
            group: "group".to_string(),
            version: "version".to_string(),
            kind: "kind".to_string(),
            api_version: "api_version".to_string(),
            plural: "plural".to_string(),
        };
    let api_resource = ApiResource::from_kube(kube_api_resource.clone());
    assert_eq!(
        api_resource.into_kube(),
        kube_api_resource
    );
}

#[test]
#[verifier(external)]
pub fn test_as_kube_ref() {
    let api_resource = ApiResource::from_kube(
        deps_hack::kube::api::ApiResource {
            group: "group".to_string(),
            version: "version".to_string(),
            kind: "kind".to_string(),
            api_version: "api_version".to_string(),
            plural: "plural".to_string(),
        },
    );
    assert_eq!(
        api_resource.as_kube_ref(),
        &deps_hack::kube::api::ApiResource {
            group: "group".to_string(),
            version: "version".to_string(),
            kind: "kind".to_string(),
            api_version: "api_version".to_string(),
            plural: "plural".to_string(),
        }
    );
}

}
