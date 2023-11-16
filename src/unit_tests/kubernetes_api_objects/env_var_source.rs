// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::container::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::volume::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for EnvVarSource
#[test]
#[verifier(external)]
pub fn test_set_field_ref() {
    let mut env_var_source = EnvVarSource::default();
    let mut object_field_selector = ObjectFieldSelector::default();
    object_field_selector.set_field_path(new_strlit("field_path").to_string());
    let mut object_field_selector_2 = ObjectFieldSelector::default();
    object_field_selector_2.set_field_path(new_strlit("field_path").to_string());
    env_var_source.set_field_ref(object_field_selector);
    assert_eq!(object_field_selector_2.into_kube(), env_var_source.into_kube().field_ref.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_default(){
    let env_var_source = EnvVarSource::default();
    assert_eq!(env_var_source.into_kube(), deps_hack::k8s_openapi::api::core::v1::EnvVarSource::default());
}

#[test]
#[verifier(external)]
pub fn test_clone(){
    let mut env_var_source = EnvVarSource::default();
    let mut object_field_selector = ObjectFieldSelector::default();
    object_field_selector.set_field_path(new_strlit("field_path").to_string());
    env_var_source.set_field_ref(object_field_selector);
    let env_var_source_clone = env_var_source.clone();
    assert_eq!(env_var_source.into_kube(), env_var_source_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube(){
    let kube_env_var_source = deps_hack::k8s_openapi::api::core::v1::EnvVarSource {
        field_ref: Some(deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector {
            field_path: "field_path".to_string(),
            ..Default::default()
        }),
        ..Default::default()
    };

    let env_var_source = EnvVarSource::from_kube(kube_env_var_source.clone());

    assert_eq!(env_var_source.into_kube(), kube_env_var_source);
}
}
