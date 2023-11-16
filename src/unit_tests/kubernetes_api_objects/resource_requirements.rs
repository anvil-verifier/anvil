// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::exec::resource_requirements::*;
use crate::vstd_ext::string_map::*;
use deps_hack::k8s_openapi::apimachinery::pkg::api::resource::Quantity;
use std::collections::BTreeMap;
use vstd::prelude::*;
use vstd::string::*;

verus! {
#[test]
#[verifier(external)]
pub fn test_default(){
    let resource_requirements = ResourceRequirements::default();
    assert_eq!(resource_requirements.into_kube(), deps_hack::k8s_openapi::api::core::v1::ResourceRequirements::default());
}

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

#[test]
#[verifier(external)]
pub fn test_set_limits() {
    let mut resource_requirements = ResourceRequirements::default();
    let mut limits = StringMap::new();
    limits.insert(new_strlit("cpu").to_string(), new_strlit("100m").to_string());
    resource_requirements.set_limits(limits.clone());
    let quantity_limits: BTreeMap<std::string::String, Quantity> = limits.into_rust_map().into_iter().map(|(k, v)| (k, Quantity(v))).collect();
    assert_eq!(quantity_limits, resource_requirements.into_kube().limits.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_clone(){
    let mut resource_requirements = ResourceRequirements::default();
    let mut requests = StringMap::new();
    requests.insert(new_strlit("cpu").to_string(), new_strlit("100m").to_string());
    resource_requirements.set_requests(requests.clone());
    let mut limits = StringMap::new();
    limits.insert(new_strlit("cpu").to_string(), new_strlit("100m").to_string());
    resource_requirements.set_limits(limits.clone());
    let resource_requirements_clone = resource_requirements.clone();
    assert_eq!(resource_requirements.into_kube(), resource_requirements_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_resource_requirements = deps_hack::k8s_openapi::api::core::v1::ResourceRequirements {
        limits: Some(
            vec![("cpu".to_string(), Quantity("100m".to_string()))]
                .into_iter()
                .collect(),
        ),
        requests: Some(
            vec![("cpu".to_string(), Quantity("100m".to_string()))]
                .into_iter()
                .collect(),
        ),
        ..Default::default()
    };

    let resource_requirements = ResourceRequirements::from_kube(kube_resource_requirements.clone());

    assert_eq!(
        resource_requirements.into_kube(),
        kube_resource_requirements
    );

}

}
