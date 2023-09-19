// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    common::*, error::ParseDynamicObjectError, marshal::*, resource::*,
};
use crate::pervasive_ext::string_map::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

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
    pub fn default() -> (label_selector: LabelSelector)
        ensures
            label_selector@ == LabelSelectorView::default(),
    {
        LabelSelector {
            inner: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_match_labels(&mut self, match_labels: StringMap)
        ensures
            self@ == old(self)@.set_match_labels(match_labels@),
    {
        self.inner.match_labels = Some(match_labels.into_rust_map());
    }
}

impl ResourceWrapper<deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector> for LabelSelector {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector) -> LabelSelector {
        LabelSelector {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector {
        self.inner
    }
}

/// LabelSelectorView is the ghost type of LabelSelector.
/// It is supposed to be used in spec and proof code.

pub struct LabelSelectorView {
    pub match_labels: Option<Map<StringView, StringView>>,
}

impl LabelSelectorView {
    pub open spec fn default() -> LabelSelectorView {
        LabelSelectorView {
            match_labels: None,
        }
    }

    pub open spec fn set_match_labels(self, match_labels: Map<StringView, StringView>) -> LabelSelectorView {
        LabelSelectorView {
            match_labels: Some(match_labels),
            ..self
        }
    }

}

impl Marshalable for LabelSelectorView {

    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

}
