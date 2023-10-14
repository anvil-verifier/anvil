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
}
