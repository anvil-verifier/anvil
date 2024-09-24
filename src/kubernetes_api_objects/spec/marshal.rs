// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub type Value = StringView;

}
