// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::spec::label_selector::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;

verus! {

// LabelSelector is used to select objects that are relevant by matching the labels.
// Labels are key/value pairs that are attached to objects such as Pods.
//
// This definition is a wrapper of LabelSelector defined at
// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/apimachinery/pkg/apis/meta/v1/label_selector.rs.
// It is supposed to be used in exec controller code.
//
// More detailed information: https://kubernetes.io/docs/concepts/overview/working-with-objects/labels/#label-selectors.

implement_field_wrapper_type!(
    LabelSelector,
    deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector,
    LabelSelectorView
);

impl LabelSelector {
    #[verifier(external_body)]
    pub fn eq(&self, other: &Self) -> (b: bool)
        ensures b == (self.view() == other.view())
    {
        self.inner == other.inner
    }

    #[verifier(external_body)]
    pub fn match_labels(&self) -> (match_labels: Option<StringMap>)
        ensures
            self@.match_labels == match_labels.deep_view(),
            match_labels is Some ==> match_labels->0@.dom().finite(),
    {
        match &self.inner.match_labels {
            Some(ml) => Some(StringMap::from_rust_map(ml.clone())),
            None => None
        }
    }

    #[verifier(external_body)]
    pub fn set_match_labels(&mut self, match_labels: StringMap)
        ensures self@ == old(self)@.with_match_labels(match_labels@),
    {
        self.inner.match_labels = Some(match_labels.into_rust_map());
    }

    // TODO: prove it and maybe move to a different lib
    #[verifier(external_body)]
    pub fn matches(&self, labels: StringMap) -> (res: bool)
        ensures res == self@.matches(labels@),
    {
        if self.match_labels().is_none() {
            true
        } else {
            let match_labels = self.match_labels().unwrap();
            let keys = match_labels.keys();
            let mut idx = 0;
            for idx in 0..keys.len()
            {
                let key = &keys[idx];
                let val = match_labels.get(key).unwrap();
                let val_or_not = labels.get(key);
                if !(val_or_not.is_some() && val_or_not.unwrap().eq(&val)) {
                    return false;
                }
            }
            true
        }
    }
}

}

implement_resource_wrapper_trait!(
    LabelSelector,
    deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector
);
