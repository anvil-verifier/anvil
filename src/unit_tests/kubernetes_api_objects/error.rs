// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::exec::dynamic::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::vstd_ext::string_map::*;
use deps_hack::chrono::{DateTime, Utc};
use deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::Time;
use vstd::prelude::*;
use vstd::string::*;

#[test]
pub fn test_apierror_fmt() {
    let error = APIError::BadRequest;
    assert_eq!(format!("{:?}", error), "BadRequest");
    let error = APIError::Conflict;
    assert_eq!(format!("{:?}", error), "Conflict");
    let error = APIError::Forbidden;
    assert_eq!(format!("{:?}", error), "Forbidden");
    let error = APIError::Invalid;
    assert_eq!(format!("{:?}", error), "Invalid");
    let error = APIError::ObjectNotFound;
    assert_eq!(format!("{:?}", error), "ObjectNotFound");
    let error = APIError::ObjectAlreadyExists;
    assert_eq!(format!("{:?}", error), "ObjectAlreadyExists");
    let error = APIError::NotSupported;
    assert_eq!(format!("{:?}", error), "NotSupported");
    let error = APIError::InternalError;
    assert_eq!(format!("{:?}", error), "InternalError");
    let error = APIError::Timeout;
    assert_eq!(format!("{:?}", error), "Timeout");
    let error = APIError::ServerTimeout;
    assert_eq!(format!("{:?}", error), "ServerTimeout");
    let error = APIError::Other;
    assert_eq!(format!("{:?}", error), "Other");
}
