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
// Tests for volume
#[test]
#[verifier(external)]
pub fn test_default() {
    let volume = Volume::default();
    assert_eq!(volume.into_kube(), deps_hack::k8s_openapi::api::core::v1::Volume::default());
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

#[test]
#[verifier(external)]
pub fn test_set_host_path() {
    let mut volume = Volume::default();
    let mut host_path_volume_source = HostPathVolumeSource::default();
    host_path_volume_source.set_path(new_strlit("path").to_string());
    volume.set_host_path(host_path_volume_source.clone());
    assert_eq!(host_path_volume_source.into_kube(), volume.into_kube().host_path.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_config_map() {
    let mut volume = Volume::default();
    let mut config_map_volume_source = ConfigMapVolumeSource::default();
    config_map_volume_source.set_name(new_strlit("name").to_string());
    volume.set_config_map(config_map_volume_source.clone());
    assert_eq!(config_map_volume_source.into_kube(), volume.into_kube().config_map.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_projected() {
    let mut volume = Volume::default();
    let mut projected_volume_source = ProjectedVolumeSource::default();
    projected_volume_source.set_sources(vec![]);
    volume.set_projected(projected_volume_source.clone());
    assert_eq!(projected_volume_source.into_kube(), volume.into_kube().projected.unwrap());
}


#[test]
#[verifier(external)]
pub fn test_set_secret() {
    let mut volume = Volume::default();
    let mut secret_volume_source = SecretVolumeSource::default();
    secret_volume_source.set_secret_name(new_strlit("name").to_string());
    volume.set_secret(secret_volume_source.clone());
    assert_eq!(secret_volume_source.into_kube(), volume.into_kube().secret.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_downward_api() {
    let mut volume = Volume::default();
    let mut downward_api_volume_source = DownwardAPIVolumeSource::default();
    downward_api_volume_source.set_items(vec![]);
    volume.set_downward_api(downward_api_volume_source.clone());
    assert_eq!(downward_api_volume_source.into_kube(), volume.into_kube().downward_api.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_empty_dir() {
    let mut volume = Volume::default();
    let empty_dir_volume_source = EmptyDirVolumeSource::default();
    volume.set_empty_dir(empty_dir_volume_source.clone());
    assert_eq!(empty_dir_volume_source.into_kube(), volume.into_kube().empty_dir.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_volume = deps_hack::k8s_openapi::api::core::v1::Volume {
        name: "name".to_string(),
        host_path: Some(deps_hack::k8s_openapi::api::core::v1::HostPathVolumeSource {
            path: "path".to_string(),
            ..Default::default()
        }),
        config_map: Some(deps_hack::k8s_openapi::api::core::v1::ConfigMapVolumeSource {
            name: Some("name".to_string()),
            ..Default::default()
        }),
        projected: Some(deps_hack::k8s_openapi::api::core::v1::ProjectedVolumeSource {
            sources: Some(vec![]),
            ..Default::default()
        }),
        secret: Some(deps_hack::k8s_openapi::api::core::v1::SecretVolumeSource {
            secret_name: Some("name".to_string()),
            ..Default::default()
        }),
        downward_api: Some(deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeSource {
            items: Some(vec![]),
            ..Default::default()
        }),
        empty_dir: Some(deps_hack::k8s_openapi::api::core::v1::EmptyDirVolumeSource {
            ..Default::default()
        }),
        ..Default::default()
    };

    let volume = Volume::from_kube(kube_volume.clone());

    assert_eq!(
        volume.into_kube(),
        kube_volume
    );

}

#[test]
#[verifier(external)]
pub fn test_clone(){
    let mut volume = Volume::default();
    let mut host_path_volume_source = HostPathVolumeSource::default();
    host_path_volume_source.set_path(new_strlit("path").to_string());
    volume.set_host_path(host_path_volume_source.clone());
    let volume_clone = volume.clone();
    assert_eq!(volume.into_kube(), volume_clone.into_kube());
}
}
