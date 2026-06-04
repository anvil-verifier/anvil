// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// LabelSelectorView is the ghost type of LabelSelector.

pub struct LabelSelectorView {
    pub match_labels: Option<IMap<StringView, StringView>>,
}

impl LabelSelectorView {
    pub open spec fn default() -> LabelSelectorView {
        LabelSelectorView {
            match_labels: None,
        }
    }

    pub open spec fn with_match_labels(self, match_labels: IMap<StringView, StringView>) -> LabelSelectorView {
        LabelSelectorView {
            match_labels: Some(match_labels),
            ..self
        }
    }

    // TODO: handle match_expressions as well
    pub open spec fn matches(self, labels: IMap<StringView, StringView>) -> bool {
        if self.match_labels is None {
            true
        } else {
            let match_labels = self.match_labels->0;
            forall |k, v| match_labels.contains_pair(k, v) ==> labels.contains_pair(k, v)
        }
    }
}


}
