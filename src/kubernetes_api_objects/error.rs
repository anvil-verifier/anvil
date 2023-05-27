// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::object_meta::*;
use deps_hack::kube;
use vstd::prelude::*;

verus! {

// TODO: implement other error types
#[is_variant]
pub enum APIError {
    ObjectNotFound,
    ObjectAlreadyExists,
    Other
}

pub struct ParseDynamicObjectError {}

}
