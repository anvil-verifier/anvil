// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive_ext::*;
use builtin::*;
use builtin_macros::*;

verus! {

// TODO: we will need to connect the Error types to real HTTP error response later
#[is_variant]
pub enum APIError {
    ObjectNotFound,
    ObjectAlreadyExists,
}

}
