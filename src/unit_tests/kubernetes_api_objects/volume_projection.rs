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
// Tests for volume projecion
#[test]
#[verifier(external)]
pub fn test_default() {
    let volume_projection = VolumeProjection::default();
    assert_eq!(volume_projection.into_kube(), deps_hack::k8s_openapi::api::core::v1::VolumeProjection::default());
}

#[test]
#[verifier(external)]
pub fn test_set_config_map() {
    let mut volume_projection = VolumeProjection::default();
    let mut config_map_projection = ConfigMapProjection::default();
    config_map_projection.set_name(new_strlit("name").to_string());
    volume_projection.set_config_map(config_map_projection.clone());
    assert_eq!(config_map_projection.into_kube(), volume_projection.into_kube().config_map.unwrap());
}

#[test]
pub fn test_set_secrets() {
    let mut volume_projection = VolumeProjection::default();
    let mut secret_projection = SecretProjection::default();
    secret_projection.set_name(new_strlit("name").to_string());
    volume_projection.set_secret(secret_projection.clone());
    assert_eq!(secret_projection.into_kube(), volume_projection.into_kube().secret.unwrap());
}
}
