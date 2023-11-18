// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::container::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::pod::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::volume::*;
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
    let empty_dir_volume_source = EmptyDirVolumeSource::default();
    let empty_dir_volume_source_clone = empty_dir_volume_source.clone();
    assert_eq!(empty_dir_volume_source.into_kube(), empty_dir_volume_source_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_empty_dir_volume_source = deps_hack::k8s_openapi::api::core::v1::EmptyDirVolumeSource{
        ..Default::default()
    };

    let empty_dir_volume_source = EmptyDirVolumeSource::from_kube(kube_empty_dir_volume_source.clone());

    assert_eq!(empty_dir_volume_source.into_kube(),
                kube_empty_dir_volume_source);
}
}
