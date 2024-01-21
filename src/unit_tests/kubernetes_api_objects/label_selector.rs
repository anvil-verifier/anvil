// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, label_selector::*, label_selector::*, object_meta::*, resource::*,
};
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for label selector
#[test]
#[verifier(external)]
pub fn test_default() {
    let label_selector = LabelSelector::default();
    assert_eq!(
        label_selector.into_kube(),
        deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector::default()
    );
}

#[test]
#[verifier(external)]
pub fn test_set_match_labels() {
    let mut label_selector = LabelSelector::default();
    let mut match_labels = StringMap::new();
    match_labels.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    match_labels.insert(new_strlit("key_2").to_string(), new_strlit("value_2").to_string());
    label_selector.set_match_labels(match_labels.clone());
    assert_eq!(
        match_labels.into_rust_map(),
        label_selector.into_kube().match_labels.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut label_selector = LabelSelector::default();
    let mut match_labels = StringMap::new();
    match_labels.insert(new_strlit("key").to_string(), new_strlit("value").to_string());
    match_labels.insert(new_strlit("key_2").to_string(), new_strlit("value_2").to_string());
    label_selector.set_match_labels(match_labels.clone());
    let label_selector_clone = label_selector.clone();
    assert_eq!(
        match_labels.into_rust_map(),
        label_selector_clone.into_kube().match_labels.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_label_selector =
        deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector {
            match_labels: Some(
                vec![
                    (
                        "key".to_string(),
                        "value".to_string(),
                    ),
                    (
                        "key_2".to_string(),
                        "value_2".to_string(),
                    ),
                ]
                .into_iter()
                .collect(),
            ),
            ..Default::default()
        };

    let label_selector = LabelSelector::from_kube(kube_label_selector.clone());

    assert_eq!(
        label_selector.into_kube(),
        kube_label_selector
    );
}
}
