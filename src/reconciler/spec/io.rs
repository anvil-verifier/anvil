// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::spec::message::*;
use vstd::prelude::*;

verus! {

#[is_variant]
pub enum RequestView<T> {
    KRequest(APIRequest),
    ExternalRequest(T),
}

impl<T> RequestView<T> {
    pub open spec fn is_k_update_request(self) -> bool {
        &&& self.is_KRequest()
        &&& self.get_KRequest_0().is_UpdateRequest()
    }

    pub open spec fn get_k_update_request(self) -> UpdateRequest {
        self.get_KRequest_0().get_UpdateRequest_0()
    }
}

#[is_variant]
pub enum ResponseView<T> {
    KResponse(APIResponse),
    ExternalResponse(T),
}

impl<T> ResponseView<T> {
    pub open spec fn is_k_get_response(self) -> bool {
        &&& self.is_KResponse()
        &&& self.get_KResponse_0().is_GetResponse()
    }

    pub open spec fn get_k_get_response(self) -> GetResponse {
        self.get_KResponse_0().get_GetResponse_0()
    }
}

#[macro_export]
macro_rules! is_some_k_get_resp_view {
    ($r:expr) => {
        $r.is_Some() && $r.get_Some_0().is_KResponse()
        && $r.get_Some_0().get_KResponse_0().is_GetResponse()
    };
}

#[macro_export]
macro_rules! is_some_k_create_resp_view {
    ($r:expr) => {
        $r.is_Some() && $r.get_Some_0().is_KResponse()
        && $r.get_Some_0().get_KResponse_0().is_CreateResponse()
    };
}

#[macro_export]
macro_rules! is_some_k_update_resp_view {
    ($r:expr) => {
        $r.is_Some() && $r.get_Some_0().is_KResponse()
        && $r.get_Some_0().get_KResponse_0().is_UpdateResponse()
    };
}

#[macro_export]
macro_rules! extract_some_k_get_resp_view {
    ($r:expr) => {
        $r.get_Some_0().get_KResponse_0().get_GetResponse_0().res
    };
}

#[macro_export]
macro_rules! extract_some_k_create_resp_view {
    ($r:expr) => {
        $r.get_Some_0().get_KResponse_0().get_CreateResponse_0().res
    };
}

#[macro_export]
macro_rules! extract_some_k_update_resp_view {
    ($r:expr) => {
        $r.get_Some_0().get_KResponse_0().get_UpdateResponse_0().res
    };
}

pub use is_some_k_get_resp_view;
pub use is_some_k_create_resp_view;
pub use is_some_k_update_resp_view;
pub use extract_some_k_get_resp_view;
pub use extract_some_k_create_resp_view;
pub use extract_some_k_update_resp_view;

}
