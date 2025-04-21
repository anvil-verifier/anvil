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

#[verifier(external_body)]
pub struct LabelSelector {
    inner: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector,
}

impl LabelSelector {

    pub spec fn view(&self) -> LabelSelectorView;

    #[verifier(external_body)]
    pub fn eq(&self, other: &Self) -> (b: bool)
        ensures b == (self.view() == other.view())
    {
        self.inner == other.inner
    }

    #[verifier(external_body)]
    pub fn default() -> (label_selector: LabelSelector)
        ensures label_selector@ == LabelSelectorView::default(),
    {
        LabelSelector {
            inner: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (label_selector: LabelSelector)
        ensures label_selector@ == self@,
    {
        LabelSelector { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn match_labels(&self) -> (match_labels: Option<StringMap>)
        ensures
            self@.match_labels.is_Some() == match_labels.is_Some(),
            match_labels.is_Some() ==> match_labels.get_Some_0()@ == self@.match_labels.get_Some_0(),
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
        ensures res == self@.matches(labels@)
    {
        if self.match_labels().is_none() {
            true
        } else {
            let match_labels = self.match_labels().unwrap();
            let keys = match_labels.keys();
            let mut idx = 0;
            while idx < match_labels.len()
            {
                let key = &keys[idx];
                let val = match_labels.get(key).unwrap();
                let val_or_not = labels.get(key);
                if !(val_or_not.is_some() && val_or_not.unwrap().eq(&val)) {
                    return false;
                }
                idx = idx + 1;
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
