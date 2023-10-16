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
// Tests for volume
#[test]
#[verifier(external)]
pub fn test_default() {
    let volume = Volume::default();
    assert_eq!(volume.into_kube(), deps_hack::k8s_openapi::api::core::v1::Volume::default());
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut volume = Volume::default();
    let mut host_path_volume_source = HostPathVolumeSource::default();
    host_path_volume_source.set_path(new_strlit("path").to_string());
    volume.set_host_path(host_path_volume_source);
    let volume_clone = volume.clone();
    assert_eq!(volume.into_kube(), volume_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_set_name() {
    let mut volume = Volume::default();
    volume.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), volume.into_kube().name);

    let mut volume = Volume::default();
    volume.set_name(new_strlit("").to_string());
    assert_eq!("".to_string(), volume.into_kube().name);
}
}
