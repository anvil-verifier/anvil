// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::container::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::volume::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for SecurityContext
#[test]
#[verifier(external)]
pub fn test_kube(){
    let kube_security_context = deps_hack::k8s_openapi::api::core::v1::SecurityContext {
        privileged: Some(true),
        ..Default::default()
    };

    let security_context = SecurityContext::from_kube(kube_security_context.clone());

    assert_eq!(security_context.into_kube(),
                kube_security_context);
}
}
