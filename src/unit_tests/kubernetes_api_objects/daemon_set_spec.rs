// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::daemon_set::*;
use crate::kubernetes_api_objects::label_selector::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::pod_template_spec::*;
use crate::kubernetes_api_objects::resource::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for daemon set spec
#[test]
#[verifier(external)]
pub fn test_default() {
    let daemon_set = DaemonSetSpec::default();
    assert_eq!(daemon_set.into_kube(), deps_hack::k8s_openapi::api::apps::v1::DaemonSetSpec::default());
}

#[test]
#[verifier(external)]
pub fn test_set_selector() {
    let mut daemon_set_spec = DaemonSetSpec::default();
    let mut label_selector = LabelSelector::default();
    let mut match_labels = StringMap::new();
    match_labels.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    label_selector.set_match_labels(match_labels.clone());
    daemon_set_spec.set_selector(label_selector.clone());
    assert_eq!(label_selector.into_kube(), daemon_set_spec.into_kube().selector);
}

#[test]
#[verifier(external)]
pub fn test_set_template() {
    let mut daemon_set_spec = DaemonSetSpec::default();
    let mut pod_template_spec = PodTemplateSpec::default();
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    pod_template_spec.set_metadata(object_meta.clone());
    daemon_set_spec.set_template(pod_template_spec.clone());
    assert_eq!(pod_template_spec.into_kube(), daemon_set_spec.into_kube().template);
}

#[test]
#[verifier(external)]
pub fn test_selector(){
    let mut daemon_set_spec = DaemonSetSpec::default();
    let mut label_selector = LabelSelector::default();
    let temp = daemon_set_spec.selector();
    if temp.into_kube() !=  LabelSelector::default().into_kube() {
        panic!("selector should be default");
    }
    let mut match_labels = StringMap::new();
    match_labels.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    label_selector.set_match_labels(match_labels.clone());
    daemon_set_spec.set_selector(label_selector.clone());
    assert_eq!(label_selector.into_kube(), daemon_set_spec.selector().into_kube());
}

#[test]
#[verifier(external)]
pub fn test_template(){
    let mut daemon_set_spec = DaemonSetSpec::default();
    let mut pod_template_spec = PodTemplateSpec::default();
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    pod_template_spec.set_metadata(object_meta.clone());
    daemon_set_spec.set_template(pod_template_spec.clone());
    assert_eq!(pod_template_spec.into_kube(), daemon_set_spec.template().into_kube());
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut daemon_set_spec = DaemonSetSpec::default();
    let mut pod_template_spec = PodTemplateSpec::default();
    let mut object_meta = ObjectMeta::default();
    object_meta.set_name(new_strlit("name").to_string());
    pod_template_spec.set_metadata(object_meta.clone());
    daemon_set_spec.set_template(pod_template_spec.clone());
    let daemon_set_spec_clone = daemon_set_spec.clone();
    assert_eq!(daemon_set_spec.into_kube(), daemon_set_spec_clone.into_kube());
}

}
