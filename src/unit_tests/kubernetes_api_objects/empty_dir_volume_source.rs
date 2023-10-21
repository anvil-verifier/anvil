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
// Tests for EmptyDirVolumeSource
#[test]
#[verifier(external)]
pub fn test_default() {
    let empty_dir_volume_source = EmptyDirVolumeSource::default();
    assert_eq!(empty_dir_volume_source.into_kube(), deps_hack::k8s_openapi::api::core::v1::EmptyDirVolumeSource::default());
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut empty_dir_volume_source = EmptyDirVolumeSource::default();
    let empty_dir_volume_source_clone = empty_dir_volume_source.clone();
    assert_eq!(empty_dir_volume_source.into_kube(), empty_dir_volume_source_clone.into_kube());
}
}
