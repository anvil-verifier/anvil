// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::container::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::pod::*;
use crate::kubernetes_api_objects::resource::*;
use crate::kubernetes_api_objects::volume::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for host path volume source
#[test]
#[verifier(external)]
pub fn test_default() {
    let host_path_volume_source = HostPathVolumeSource::default();
    assert_eq!(host_path_volume_source.into_kube(), deps_hack::k8s_openapi::api::core::v1::HostPathVolumeSource::default());
}

#[test]
#[verifier(external)]
pub fn test_set_path() {
    let mut host_path_volume_source = HostPathVolumeSource::default();
    host_path_volume_source.set_path(new_strlit("path").to_string());
    assert_eq!("path".to_string(), host_path_volume_source.into_kube().path);
}
}
