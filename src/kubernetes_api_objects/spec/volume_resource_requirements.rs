// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub struct VolumeResourceRequirementsView {
    pub limits: Option<Map<StringView, StringView>>,
    pub requests: Option<Map<StringView, StringView>>,
}

impl VolumeResourceRequirementsView {
    pub open spec fn default() -> VolumeResourceRequirementsView {
        VolumeResourceRequirementsView {
            limits: None,
            requests: None,
        }
    }

    pub open spec fn with_limits(self, limits: Map<StringView, StringView>) -> VolumeResourceRequirementsView {
        VolumeResourceRequirementsView {
            limits: Some(limits),
            ..self
        }
    }

    pub open spec fn with_requests(self, requests: Map<StringView, StringView>) -> VolumeResourceRequirementsView {
        VolumeResourceRequirementsView {
            requests: Some(requests),
            ..self
        }
    }
}

}
