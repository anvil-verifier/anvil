// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::marshal::*;
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
    pub fn default() -> (object_meta: LabelSelector)
        ensures
            object_meta@ == LabelSelectorView::default(),
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
        self.inner.match_labels = std::option::Option::Some(match_labels.into_rust_map());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector {
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
            match_labels: Option::None,
        }
    }

    pub open spec fn set_match_labels(self, match_labels: Map<StringView, StringView>) -> LabelSelectorView {
        LabelSelectorView {
            match_labels: Option::Some(match_labels),
            ..self
        }
    }

    pub open spec fn match_labels_field() -> nat {0}
}

impl Marshalable for LabelSelectorView {
    open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::match_labels_field(), if self.match_labels.is_None() { Value::Null } else {
                    Value::StringStringMap(self.match_labels.get_Some_0())
                })
        )
    }

    open spec fn unmarshal(value: Value) -> Result<Self, Error> {
        if value.is_Object() {
            let obj_value = value.get_Object_0();
            if obj_value[Self::match_labels_field()].is_Null() {
                let res = LabelSelectorView { match_labels: Option::None, };
                return Result::Ok(res);
            } else if obj_value[Self::match_labels_field()].is_StringStringMap() {
                let res = LabelSelectorView {
                    match_labels: Option::Some(obj_value[Self::match_labels_field()].get_StringStringMap_0())
                };
                return Result::Ok(res);
            }
        }
        return Result::Err(Error::TypeError);
    }

    proof fn marshal_preserves_integrity() {}
}

}
