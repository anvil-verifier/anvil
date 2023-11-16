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
// Tests for config map volume source
#[test]
#[verifier(external)]
pub fn test_default() {
    let config_map_volume_source = ConfigMapVolumeSource::default();
    assert_eq!(config_map_volume_source.into_kube(), deps_hack::k8s_openapi::api::core::v1::ConfigMapVolumeSource::default());
}

#[test]
#[verifier(external)]
pub fn test_set_name() {
    let mut config_map_volume_source = ConfigMapVolumeSource::default();
    config_map_volume_source.set_name(new_strlit("name").to_string());
    assert_eq!("name".to_string(), config_map_volume_source.into_kube().name.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_clone(){
    let mut config_map_volume_source = ConfigMapVolumeSource::default();
    config_map_volume_source.set_name(new_strlit("name").to_string());
    let config_map_volume_source_clone = config_map_volume_source.clone();
    assert_eq!(config_map_volume_source.into_kube(), config_map_volume_source_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube(){
    let kube_config_map_volume_source = deps_hack::k8s_openapi::api::core::v1::ConfigMapVolumeSource{
        default_mode: None,
        items: None,
        name: Some("name".to_string()),
        optional: None,
    };

    let config_map_volume_source = ConfigMapVolumeSource::from_kube(kube_config_map_volume_source.clone());

    assert_eq!(config_map_volume_source.into_kube(),
                kube_config_map_volume_source);
}

}
