// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::container::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::pod::*;
use crate::kubernetes_api_objects::pod_template_spec::*;
use crate::kubernetes_api_objects::resource::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for pod template spec
#[test]
#[verifier(external)]
pub fn test_default() {
    let pod_template_spec = PodTemplateSpec::default();
    assert_eq!(pod_template_spec.into_kube(), deps_hack::k8s_openapi::api::core::v1::PodTemplateSpec::default());
}

#[test]
#[verifier(external)]
pub fn test_set_metadata() {
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());

    let mut pod_template_spec = PodTemplateSpec::default();
    pod_template_spec.set_metadata(object_meta.clone());
    assert_eq!(object_meta.into_kube(), pod_template_spec.into_kube().metadata.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_set_spec() {
    let mut pod_spec = PodSpec::default();
    let mut container = Container::default();
    container.set_name(new_strlit("name").to_string());
    pod_spec.set_containers(vec![container.clone()]);
    let mut pod_template_spec = PodTemplateSpec::default();
    pod_template_spec.set_spec(pod_spec.clone());
    assert_eq!(pod_spec.into_kube(), pod_template_spec.into_kube().spec.unwrap());
}
}
