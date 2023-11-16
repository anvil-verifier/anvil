// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::api_resource::*;
use crate::kubernetes_api_objects::exec::config_map::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

#[test]
#[verifier(external)]
pub fn test_set_metadata() {
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());

    let mut config_map = ConfigMap::default();
    config_map.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), config_map.into_kube().metadata);
}

#[test]
#[verifier(external)]
pub fn test_set_data(){
    let mut config_map = ConfigMap::default();
    let mut data = StringMap::new();
    data.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    config_map.set_data(data.clone());
    assert_eq!(data.into_rust_map(), config_map.into_kube().data.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_default(){
    let config_map = ConfigMap::default();
    assert_eq!(config_map.into_kube(), deps_hack::k8s_openapi::api::core::v1::ConfigMap::default());
}

#[test]
#[verifier(external)]
pub fn test_clone(){
    let mut config_map = ConfigMap::default();
    let mut data = StringMap::new();
    data.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    config_map.set_data(data.clone());
    let config_map_clone = config_map.clone();
    assert_eq!(config_map.into_kube(), config_map_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_metadata(){
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());

    let mut config_map = ConfigMap::default();
    config_map.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), config_map.metadata().into_kube());
}

#[test]
#[verifier(external)]
pub fn test_data(){
    let mut config_map = ConfigMap::default();
    let mut data = StringMap::new();
    data.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    config_map.set_data(data.clone());
    assert_eq!(data.into_rust_map(), config_map.data().unwrap().into_rust_map());
}

#[test]
#[verifier(external)]
pub fn test_api_resource(){
    let api_resource = ConfigMap::api_resource();
    assert_eq!(api_resource.into_kube().kind, "ConfigMap");
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_config_map = deps_hack::k8s_openapi::api::core::v1::ConfigMap {
        metadata:
            deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                name: Some("name".to_string()),
                ..Default::default()
            },
        data: Some(
            vec![(
                "key".to_string(),
                "value".to_string(),
            )]
            .into_iter()
            .collect(),
        ),
        ..Default::default()
    };
    let config_map = ConfigMap::from_kube(
        kube_config_map.clone(),
    );

    assert_eq!(config_map.into_kube(),
                kube_config_map);
}

#[test]
#[verifier(external)]
pub fn test_marshal() {
    let kube_config_map = deps_hack::k8s_openapi::api::core::v1::ConfigMap {
        metadata:
            deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                name: Some("name".to_string()),
                ..Default::default()
            },
        data: Some(
            vec![(
                "key".to_string(),
                "value".to_string(),
            )]
            .into_iter()
            .collect(),
        ),
        ..Default::default()
    };

    let config_map = ConfigMap::from_kube(
        kube_config_map.clone(),
    );

    assert_eq!(
        kube_config_map,
        ConfigMap::unmarshal(config_map.marshal()).unwrap().into_kube()
    );
}

}
