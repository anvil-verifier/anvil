// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::toleration::*;
use crate::vstd_ext::string_map::*;
use deps_hack::chrono::{DateTime, Utc};
use deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::Time;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for toleration
#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_toleration =
        deps_hack::k8s_openapi::api::core::v1::Toleration {
            key: Some("key".to_string()),
            operator: Some("operator".to_string()),
            value: Some("value".to_string()),
            effect: Some("effect".to_string()),
            toleration_seconds: Some(1),
            ..Default::default()
        };
    let toleration = Toleration::from_kube(kube_toleration.clone());
    assert_eq!(
        toleration.into_kube(),
        kube_toleration
    );
}
}
