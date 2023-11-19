// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::affinity::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::vstd_ext::string_map::*;
use deps_hack::chrono::{DateTime, Utc};
use deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::Time;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for affinity
#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_affinity = deps_hack::k8s_openapi::api::core::v1::Affinity {
        node_affinity: Some(deps_hack::k8s_openapi::api::core::v1::NodeAffinity {
            preferred_during_scheduling_ignored_during_execution: None,
            ..Default::default()
        }),
        pod_affinity: Some(deps_hack::k8s_openapi::api::core::v1::PodAffinity {
            preferred_during_scheduling_ignored_during_execution: None,
            ..Default::default()
        }),
        ..Default::default()
    };

    let affinity = Affinity::from_kube(kube_affinity.clone());

    assert_eq!(affinity.into_kube(), kube_affinity);
}
}
