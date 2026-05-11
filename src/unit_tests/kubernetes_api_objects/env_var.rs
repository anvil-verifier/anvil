// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::container::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::volume::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

#[test]
pub fn test_default() {
    let env = EnvVar::default();
    assert_eq!(
        env.into_kube(),
        k8s_openapi::api::core::v1::EnvVar::default()
    );
}

#[test]
pub fn test_clone() {
    let mut env = EnvVar::default();
    env.set_name("name".to_string());
    env.set_value("value".to_string());
    let env_clone = env.clone();
    assert_eq!(env.into_kube(), env_clone.into_kube());
}

#[test]
pub fn test_set_name() {
    let mut env_var = EnvVar::default();
    env_var.set_name("name".to_string());
    assert_eq!("name".to_string(), env_var.into_kube().name);
}

#[test]
pub fn test_set_value() {
    let mut env_var = EnvVar::default();
    env_var.set_value("value".to_string());
    assert_eq!("value".to_string(), env_var.into_kube().value.unwrap());
}

#[test]
pub fn test_set_value_from() {
    let mut env_var = EnvVar::default();
    let mut env_var_source = EnvVarSource::default();
    let mut object_field_selector = ObjectFieldSelector::default();
    object_field_selector.set_field_path("field_path".to_string());
    env_var_source.set_field_ref(object_field_selector);
    env_var.set_value_from(env_var_source.clone());
    assert_eq!(
        env_var_source.into_kube(),
        env_var.into_kube().value_from.unwrap()
    );
}

#[test]
pub fn test_kube() {
    let kube_env_var = k8s_openapi::api::core::v1::EnvVar {
        name: "name".to_string(),
        value: Some("value".to_string()),
        value_from: Some(k8s_openapi::api::core::v1::EnvVarSource {
            field_ref: Some(k8s_openapi::api::core::v1::ObjectFieldSelector {
                field_path: "field_path".to_string(),
                ..Default::default()
            }),
            ..Default::default()
        }),
        ..Default::default()
    };

    let env_var = EnvVar::from_kube(kube_env_var.clone());

    assert_eq!(env_var.into_kube(), kube_env_var);
}
