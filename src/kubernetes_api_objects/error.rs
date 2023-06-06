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
    BadRequest,
    Conflict,
    ObjectNotFound,
    ObjectAlreadyExists,
    NotSupported,
    Other
}

pub enum ParseDynamicObjectError {
    MissingField,
    UnexpectedType,
    UnmarshalError,
    ExecError,
}

impl APIError {
    pub fn is_object_not_found(&self) -> (res: bool)
        ensures res <==> self.is_ObjectNotFound(),
    {
        match self {
            APIError::ObjectNotFound => true,
            _ => false,
        }
    }
}

}
