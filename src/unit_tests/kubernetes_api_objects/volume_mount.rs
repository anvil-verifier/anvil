// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::container::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::resource_requirements::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for volume monts
#[test]
#[verifier(external)]
pub fn test_set_mount_path() {
    let mut volume_mount = VolumeMount::default();
    volume_mount.set_mount_path(new_strlit("mount_path").to_string());
    assert_eq!("mount_path".to_string(), volume_mount.into_kube().mount_path);
}

#[test]
#[verifier(external)]
pub fn test_set_name() {
    let mut volume_mount = VolumeMount::default();
    volume_mount.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), volume_mount.into_kube().name);
}

#[test]
#[verifier(external)]
pub fn test_set_read_only() {
    let mut volume_mount = VolumeMount::default();
    volume_mount.set_read_only(true);
    assert_eq!(true, volume_mount.into_kube().read_only.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_sub_path() {
    let mut volume_mount = VolumeMount::default();
    volume_mount.set_sub_path(new_strlit("sub_path").to_string());
    assert_eq!("sub_path".to_string(), volume_mount.into_kube().sub_path.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_default(){
    let volume_mount = VolumeMount::default();
    assert_eq!(volume_mount.into_kube(), deps_hack::k8s_openapi::api::core::v1::VolumeMount::default());
}

#[test]
#[verifier(external)]
pub fn test_new_with(){
    let volume_mount = VolumeMount::new_with(
        new_strlit("mount_path").to_string(),
        new_strlit("name").to_string(),
    );
    assert_eq!(volume_mount.into_kube(), deps_hack::k8s_openapi::api::core::v1::VolumeMount{
        mount_path: "mount_path".to_string(),
        name: "name".to_string(),
        ..Default::default()
    });
}

#[test]
#[verifier(external)]
pub fn test_kube(){
    let kube_volume_mount = deps_hack::k8s_openapi::api::core::v1::VolumeMount{
        mount_path: "mount_path".to_string(),
        name: "name".to_string(),
        sub_path: Some("sub_path".to_string()),
        read_only: Some(true),
        ..Default::default()
    };

    let volume_mount = VolumeMount::from_kube(kube_volume_mount.clone());

    assert_eq!(volume_mount.into_kube(), kube_volume_mount.clone());
}
}
