// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::container::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

#[test]
#[verifier(external)]
pub fn test_set_image() {
    println!("Testing set_image()...");
    let mut container = Container::default();
    container.set_image(new_strlit("image").to_string());
    assert_eq!("image".to_string(), container.into_kube().image.unwrap());
}

#[test]
#[verifier(external)]
pub fn set_name() {
    println!("Testing set_name()...");
    let mut container = Container::default();
    container.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), container.into_kube().name);
}

// Tests for volume monts
#[test]
#[verifier(external)]
pub fn set_mount_path() {
    println!("Testing set_mount_path()...");
    let mut volume_mount = VolumeMount::default();
    volume_mount.set_mount_path(new_strlit("mount_path").to_string());
    assert_eq!("mount_path".to_string(), volume_mount.into_kube().mount_path);
}

#[test]



}
