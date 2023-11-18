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
// Tests for downwardAPI volume source
#[test]
#[verifier(external)]
pub fn test_default() {
    let downward_api_volume_source = DownwardAPIVolumeSource::default();
    assert_eq!(downward_api_volume_source.into_kube(), deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeSource::default());
}

#[test]
#[verifier(external)]
pub fn test_set_items() {
    let mut downward_api_volume_source = DownwardAPIVolumeSource::default();
    let downward_api_volume_file_gen = || {
        let mut downward_api_volume_file_1 = DownwardAPIVolumeFile::default();
        let mut downward_api_volume_file_2 = DownwardAPIVolumeFile::default();
        let mut downward_api_volume_files = Vec::new();
        downward_api_volume_file_1.set_path(new_strlit("path1").to_string());
        downward_api_volume_file_2.set_path(new_strlit("path2").to_string());
        downward_api_volume_files.push(downward_api_volume_file_1);
        downward_api_volume_files.push(downward_api_volume_file_2);
        downward_api_volume_files
    };
    downward_api_volume_source.set_items(downward_api_volume_file_gen());
    assert_eq!(
        downward_api_volume_file_gen()
            .into_iter()
            .map(|s: DownwardAPIVolumeFile| s.into_kube())
            .collect::<Vec<_>>(),
        downward_api_volume_source.into_kube().items.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_clone(){
    let mut downward_api_volume_source = DownwardAPIVolumeSource::default();
    let downward_api_volume_file_gen = || {
        let mut downward_api_volume_file_1 = DownwardAPIVolumeFile::default();
        let mut downward_api_volume_file_2 = DownwardAPIVolumeFile::default();
        let mut downward_api_volume_files = Vec::new();
        downward_api_volume_file_1.set_path(new_strlit("path1").to_string());
        downward_api_volume_file_2.set_path(new_strlit("path2").to_string());
        downward_api_volume_files.push(downward_api_volume_file_1);
        downward_api_volume_files.push(downward_api_volume_file_2);
        downward_api_volume_files
    };
    downward_api_volume_source.set_items(downward_api_volume_file_gen());
    let downward_api_volume_source_clone = downward_api_volume_source.clone();
    assert_eq!(downward_api_volume_source.into_kube(), downward_api_volume_source_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_downward_api_volume_source = deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeSource{
        default_mode: None,
        items: Some(vec![deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeFile{
            field_ref: Some(deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector{
                api_version: None,
                field_path: "field_path".to_string(),
            }),
            mode: None,
            path: "path".to_string(),
            resource_field_ref: None,
        }]),
    };

    let downward_api_volume_source = DownwardAPIVolumeSource::from_kube(kube_downward_api_volume_source.clone());
    assert_eq!(downward_api_volume_source.into_kube(),
                kube_downward_api_volume_source);
}
}
