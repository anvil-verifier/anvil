// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::daemon_set::*;
use crate::kubernetes_api_objects::exec::label_selector::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::pod_template_spec::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for daemon set status
#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_daemon_set_status =
        deps_hack::k8s_openapi::api::apps::v1::DaemonSetStatus {
            current_number_scheduled: 1,
            number_misscheduled: 2,
            desired_number_scheduled: 3,
            number_ready: 4,
            ..Default::default()
        };
    let daemon_set_status = DaemonSetStatus::from_kube(kube_daemon_set_status.clone());
    assert_eq!(
        daemon_set_status.into_kube(),
        kube_daemon_set_status
    );
}

#[test]
#[verifier(external)]
pub fn test_number_ready() {
    let daemon_set_status = DaemonSetStatus::from_kube(
        deps_hack::k8s_openapi::api::apps::v1::DaemonSetStatus {
            number_ready: 1,
            ..Default::default()
        },
    );
    assert_eq!(
        1,
        daemon_set_status.into_kube().number_ready
    );
}

}
