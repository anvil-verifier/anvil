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

#[test]
#[verifier(external)]
pub fn test_clone(){
    let mut host_path_volume_source = HostPathVolumeSource::default();
    host_path_volume_source.set_path(new_strlit("path").to_string());
    let host_path_volume_source_clone = host_path_volume_source.clone();
    assert_eq!(host_path_volume_source.into_kube(), host_path_volume_source_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_host_path_volume_source = deps_hack::k8s_openapi::api::core::v1::HostPathVolumeSource{
        path: "path".to_string(),
        ..Default::default()
    };

    let host_path_volume_source = HostPathVolumeSource::from_kube(kube_host_path_volume_source.clone());

    assert_eq!(host_path_volume_source.into_kube(),
        kube_host_path_volume_source);
}
}
