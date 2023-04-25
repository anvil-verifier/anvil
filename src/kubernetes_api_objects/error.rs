// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::object_meta::*;
use kube;
use vstd::prelude::*;

verus! {

// TODO: implement other error types
#[is_variant]
pub enum APIError {
    ObjectNotFound,
    ObjectAlreadyExists,
    Other
}

#[verifier(external)]
pub fn kube_error_to_ghost(error: kube::Error) -> APIError {
    match error {
        kube::Error::Api(error_resp) => {
            if error_resp.code == 404 {
                APIError::ObjectNotFound
            } else if error_resp.code == 403 {
                APIError::ObjectAlreadyExists
            } else {
                APIError::Other
            }
        },
        _ => APIError::Other,
    }
}

}
