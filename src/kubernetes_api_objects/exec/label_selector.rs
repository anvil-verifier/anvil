// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::spec::label_selector::*;
use crate::vstd_ext::{string_map::*, string_view::*};
use vstd::{prelude::*, string::*};

verus! {

/// LabelSelector is used to select objects that are relevant by matching the labels.
/// Labels are key/value pairs that are attached to objects such as Pods.
///
/// This definition is a wrapper of LabelSelector defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/apimachinery/pkg/apis/meta/v1/label_selector.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/overview/working-with-objects/labels/#label-selectors.

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
    pub fn set_match_labels(&mut self, match_labels: StringMap)
        ensures self@ == old(self)@.set_match_labels(match_labels@),
    {
        self.inner.match_labels = Some(match_labels.into_rust_map());
    }
}

#[verifier(external)]
impl ResourceWrapper<deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector> for LabelSelector {
    fn from_kube(inner: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector) -> LabelSelector { LabelSelector { inner: inner } }

    fn into_kube(self) -> deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector { self.inner }
}

}
