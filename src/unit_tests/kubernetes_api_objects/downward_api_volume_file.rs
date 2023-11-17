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
// Tests for downwardAPI volume file
#[test]
#[verifier(external)]
pub fn test_default() {
    let downward_api_volume_file = DownwardAPIVolumeFile::default();
    assert_eq!(downward_api_volume_file.into_kube(), deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeFile::default());
}

#[test]
#[verifier(external)]
pub fn test_set_field_ref() {
    let mut downward_api_volume_file = DownwardAPIVolumeFile::default();
    let mut object_field_selector = ObjectFieldSelector::default();
    object_field_selector.set_field_path(new_strlit("field_path").to_string());
    downward_api_volume_file.set_field_ref(object_field_selector.clone());
    assert_eq!(
        object_field_selector.into_kube(),
        downward_api_volume_file.into_kube().field_ref.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_set_path() {
    let mut downward_api_volume_file = DownwardAPIVolumeFile::default();
    downward_api_volume_file.set_path(new_strlit("path").to_string());
    assert_eq!("path".to_string(), downward_api_volume_file.into_kube().path);
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_downward_api_volume_file = deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeFile{
        field_ref: Some(deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector{
            api_version: None,
            field_path: "field_path".to_string(),
        }),
        mode: None,
        path: "path".to_string(),
        resource_field_ref: None,
    };

    let downward_api_volume_file = DownwardAPIVolumeFile::from_kube(kube_downward_api_volume_file.clone());

    assert_eq!(downward_api_volume_file.into_kube(),
                kube_downward_api_volume_file);
}
}
