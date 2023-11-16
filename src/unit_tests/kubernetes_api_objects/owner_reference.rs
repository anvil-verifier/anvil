// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::owner_reference::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::vstd_ext::string_map::*;
use deps_hack::chrono::{DateTime, Utc};
use deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::Time;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for owner reference
#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_owner_reference =
        deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference {
            api_version: "api_version".to_string(),
            kind: "kind".to_string(),
            name: "name".to_string(),
            uid: "uid".to_string(),
            ..Default::default()
        };
    let owner_reference = OwnerReference::from_kube(kube_owner_reference.clone());
    assert_eq!(
        owner_reference.into_kube(),
        kube_owner_reference
    );
}
}
