// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{common::*, resource::*};
use crate::vstd_ext::string_map::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

// LabelSelectorView is the ghost type of LabelSelector.

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

    // TODO: handle match_expressions as well
    pub open spec fn matches(self, labels: Map<StringView, StringView>) -> bool {
        if self.match_labels.is_None() {
            true
        } else {
            let match_labels = self.match_labels.get_Some_0();
            forall |k, v| match_labels.contains_pair(k, v) ==> labels.contains_pair(k, v)
        }
    }
}


}
