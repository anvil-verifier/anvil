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
// Tests for key to path
#[test]
#[verifier(external)]
pub fn test_default() {
    let key_to_path = KeyToPath::default();
    assert_eq!(key_to_path.into_kube(), deps_hack::k8s_openapi::api::core::v1::KeyToPath::default());
}

#[test]
#[verifier(external)]
pub fn test_set_key() {
    let mut key_to_path = KeyToPath::default();
    key_to_path.set_key(new_strlit("key").to_string());
    assert_eq!("key".to_string(), key_to_path.into_kube().key);
}

#[test]
#[verifier(external)]
pub fn test_set_path() {
    let mut key_to_path = KeyToPath::default();
    key_to_path.set_path(new_strlit("path").to_string());
    assert_eq!("path".to_string(), key_to_path.into_kube().path);
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_key_to_path = deps_hack::k8s_openapi::api::core::v1::KeyToPath{
        key: "key".to_string(),
        path: "path".to_string(),
        ..Default::default()
    };

    let key_to_path = KeyToPath::from_kube(kube_key_to_path.clone());
    assert_eq!(key_to_path.into_kube(),
        kube_key_to_path);
}
}
