// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{common::*, dynamic::*, object_meta::*, resource::*};
use crate::vstd_ext::string_map::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// TolerationView is the ghost type of Toleration.


pub struct TolerationView {}

impl TolerationView {}

}
