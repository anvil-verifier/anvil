// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::affinity::*;
use crate::kubernetes_api_objects::exec::container::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::pod::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::toleration::*;
use crate::kubernetes_api_objects::exec::volume::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for pod security context
#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_pod_security_context =
        deps_hack::k8s_openapi::api::core::v1::PodSecurityContext {
            fs_group: Some(1024),
            run_as_group: Some(1024),
            run_as_non_root: Some(true),
            run_as_user: Some(1024),
            se_linux_options: Some(
                deps_hack::k8s_openapi::api::core::v1::SELinuxOptions {
                    level: Some("level".to_string()),
                    role: Some("role".to_string()),
                    type_: Some("type_".to_string()),
                    user: Some("user".to_string()),
                    ..Default::default()
                },
            ),
            supplemental_groups: Some(
                vec![
                    1024,
                    1024,
                ],
            ),
            windows_options: Some(
                deps_hack::k8s_openapi::api::core::v1::WindowsSecurityContextOptions {
                    gmsa_credential_spec: Some("gmsa_credential_spec".to_string()),
                    gmsa_credential_spec_name: Some("gmsa_credential_spec_name".to_string()),
                    run_as_user_name: Some("run_as_user_name".to_string()),
                    ..Default::default()
                },
            ),
            ..Default::default()
        };

    let pod_security_context = PodSecurityContext::from_kube(kube_pod_security_context.clone());
    assert_eq!(
        pod_security_context.into_kube(),
        kube_pod_security_context
    );
}
}
