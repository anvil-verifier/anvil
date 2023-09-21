// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::kubernetes_api_objects::resource_requirements::*;
use crate::pervasive_ext::string_map::*;
use deps_hack::k8s_openapi::apimachinery::pkg::api::resource::Quantity;
use std::collections::BTreeMap;
use vstd::prelude::*;
use vstd::string::*;

verus! {
#[test]
#[verifier(external)]
pub fn test_set_requests(){
    let mut resource_requirements = ResourceRequirements::default();
    let mut requests = StringMap::new();
    requests.insert(new_strlit("cpu").to_string(), new_strlit("100m").to_string());
    resource_requirements.set_requests(requests.clone());
    let quantity_request: BTreeMap<std::string::String, Quantity> = requests.into_rust_map().into_iter().map(|(k, v)| (k, Quantity(v))).collect();
    assert_eq!(quantity_request, resource_requirements.into_kube().requests.unwrap());
}
}
