// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{common::*, object_meta::*};
use deps_hack::kube;
use vstd::prelude::*;

verus! {

// TODO: implement other error types
#[is_variant]
pub enum APIError {
    BadRequest,
    Conflict,
    Forbidden,
    Invalid,
    ObjectNotFound,
    ObjectAlreadyExists,
    NotSupported,
    InternalError,
    ServerTimeout,
    Other
}

impl std::fmt::Debug for APIError {
    #[verifier(external)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            APIError::BadRequest => write!(f, "BadRequest"),
            APIError::Conflict => write!(f, "Conflict"),
            APIError::Forbidden => write!(f, "Forbidden"),
            APIError::Invalid => write!(f, "Invalid"),
            APIError::ObjectNotFound => write!(f, "ObjectNotFound"),
            APIError::ObjectAlreadyExists => write!(f, "ObjectAlreadyExists"),
            APIError::NotSupported => write!(f, "NotSupported"),
            APIError::InternalError => write!(f, "InternalError"),
            APIError::ServerTimeout => write!(f, "ServerTimeout"),
            APIError::Other => write!(f, "Other"),
        }
    }
}

pub enum ParseDynamicObjectError {
    MissingField,
    UnexpectedType,
    UnmarshalError,
    ExecError,
}

impl std::fmt::Debug for ParseDynamicObjectError {
    #[verifier(external)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            ParseDynamicObjectError::MissingField => write!(f, "MissingField"),
            ParseDynamicObjectError::UnexpectedType => write!(f, "UnexpectedType"),
            ParseDynamicObjectError::UnmarshalError => write!(f, "UnmarshalError"),
            ParseDynamicObjectError::ExecError => write!(f, "ExecError"),
        }
    }
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
