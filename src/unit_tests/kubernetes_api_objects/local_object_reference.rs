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
// Tests for LocalObjectReference
#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_local_object_reference = deps_hack::k8s_openapi::api::core::v1::LocalObjectReference {
        name: Some("name".to_string()),
    };

    let local_object_reference = LocalObjectReference::from_kube(kube_local_object_reference.clone());

    assert_eq!(local_object_reference.into_kube(),
                kube_local_object_reference);
}
}
