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
// Tests for secret volume source
#[test]
#[verifier(external)]
pub fn test_default() {
    let secret_volume_source = SecretVolumeSource::default();
    assert_eq!(secret_volume_source.into_kube(), deps_hack::k8s_openapi::api::core::v1::SecretVolumeSource::default());
}

#[test]
#[verifier(external)]
pub fn test_set_secret_name() {
    let mut secret_volume_source = SecretVolumeSource::default();
    secret_volume_source.set_secret_name(new_strlit("secret_name").to_string());
    assert_eq!("secret_name".to_string(), secret_volume_source.into_kube().secret_name.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_clone(){
    let mut secret_volume_source = SecretVolumeSource::default();
    secret_volume_source.set_secret_name(new_strlit("secret_name").to_string());
    let secret_volume_source_clone = secret_volume_source.clone();
    assert_eq!(secret_volume_source.into_kube(), secret_volume_source_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_secret_volume_source =
        deps_hack::k8s_openapi::api::core::v1::SecretVolumeSource{
            secret_name: Some("secret_name".to_string()),
            ..Default::default()
        };

    let secret_volume_source = SecretVolumeSource::from_kube(kube_secret_volume_source.clone());

    assert_eq!(
        secret_volume_source.into_kube(),
        kube_secret_volume_source
    );
}
}
