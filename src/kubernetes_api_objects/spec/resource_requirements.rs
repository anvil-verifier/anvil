// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub struct ResourceRequirementsView {
    pub limits: Option<IMap<StringView, StringView>>,
    pub requests: Option<IMap<StringView, StringView>>,
}

impl ResourceRequirementsView {
    pub open spec fn default() -> ResourceRequirementsView {
        ResourceRequirementsView {
            limits: None,
            requests: None,
        }
    }

    pub open spec fn with_limits(self, limits: IMap<StringView, StringView>) -> ResourceRequirementsView {
        ResourceRequirementsView {
            limits: Some(limits),
            ..self
        }
    }

    pub open spec fn with_requests(self, requests: IMap<StringView, StringView>) -> ResourceRequirementsView {
        ResourceRequirementsView {
            requests: Some(requests),
            ..self
        }
    }
}

}
