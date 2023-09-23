// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::config_map::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
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

}
