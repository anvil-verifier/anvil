// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::dynamic::*;
use crate::pervasive_ext::string_map::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

#[verifier(external_body)]
pub struct LabelSelector {
    inner: k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector,
}

impl LabelSelector {
    pub spec fn view(&self) -> LabelSelectorView;

    #[verifier(external_body)]
    pub fn default() -> (object_meta: LabelSelector)
        ensures
            object_meta@ == LabelSelectorView::default(),
    {
        LabelSelector {
            inner: k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector::default(),
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
    pub fn into_kube(self) -> k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector {
        self.inner
    }
}

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

    pub open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::match_labels_field(), if self.match_labels.is_None() {Value::Null} else {
                    Value::StringStringMap(self.match_labels.get_Some_0())
                })
        )
    }

    pub open spec fn unmarshal(value: Value) -> Self {
        LabelSelectorView {
            match_labels: if value.get_Object_0()[Self::match_labels_field()].is_Null() {Option::None} else {
                Option::Some(value.get_Object_0()[Self::match_labels_field()].get_StringStringMap_0())
            },
        }
    }

    proof fn integrity_check()
        ensures forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()),
    {}

    pub open spec fn match_labels_field() -> nat {0}
}

}
