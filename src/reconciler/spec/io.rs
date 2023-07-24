// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::spec::message::*;
use vstd::prelude::*;

verus! {

#[is_variant]
pub enum RequestView<T> {
    KRequest(APIRequest),
    ExternalRequest(T),
}

#[is_variant]
pub enum ResponseView<T> {
    KResponse(APIResponse),
    ExternalResponse(T),
}

}
