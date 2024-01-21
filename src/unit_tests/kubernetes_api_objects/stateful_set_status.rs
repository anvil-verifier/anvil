// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, label_selector::*, object_meta::*, persistent_volume_claim::*,
    pod_template_spec::*, resource::*, stateful_set::*,
};
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for stateful set status
#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_stateful_set_status =
        deps_hack::k8s_openapi::api::apps::v1::StatefulSetStatus {
            replicas: 1,
            ready_replicas: Some(1),
            current_replicas: Some(1),
            updated_replicas: Some(1),
            current_revision: Some("current_revision".to_string()),
            update_revision: Some("update_revision".to_string()),
            collision_count: Some(1),
            observed_generation: Some(1),
            ..Default::default()
        };

    let stateful_set_status = StatefulSetStatus::from_kube(kube_stateful_set_status.clone());

    assert_eq!(
        stateful_set_status.into_kube(),
        kube_stateful_set_status
    );
}

#[test]
#[verifier(external)]
pub fn test_ready_replicas() {
    let stateful_set_status = StatefulSetStatus::from_kube(
        deps_hack::k8s_openapi::api::apps::v1::StatefulSetStatus {
            replicas: 1,
            ready_replicas: Some(1),
            ..Default::default()
        },
    );
    assert_eq!(
        1,
        stateful_set_status.into_kube().ready_replicas.unwrap()
    );
}

}
