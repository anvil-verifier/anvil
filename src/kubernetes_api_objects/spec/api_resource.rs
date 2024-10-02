// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::common::*;
use vstd::prelude::*;

verus! {

// ApiResourceView is the ghost type of ApiResource.


pub struct ApiResourceView {
    pub kind: Kind,
}

}
