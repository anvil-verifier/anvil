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
pub fn test_kube() {
    let downward_api_volume_file = DownwardAPIVolumeFile::from_kube(deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeFile{
        field_ref: Some(deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector{
            api_version: None,
            field_path: "field_path".to_string(),
        }),
        mode: None,
        path: "path".to_string(),
        resource_field_ref: None,
    });

    assert_eq!(downward_api_volume_file.into_kube(),
        deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeFile{
            field_ref: Some(deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector{
                api_version: None,
                field_path: "field_path".to_string(),
            }),
            mode: None,
            path: "path".to_string(),
            resource_field_ref: None,
        });
}
}
