// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive_ext::string_view::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub open spec fn cm_suffix() -> StringView {
    new_strlit("-cm")@
}

pub open spec fn sts_suffix() -> StringView {
    new_strlit("-sts")@
}

pub open spec fn pod_suffix() -> StringView {
    new_strlit("-pod")@
}

pub open spec fn vol_suffix() -> StringView {
    new_strlit("-vol")@
}

pub open spec fn default_ns() -> StringView {
    new_strlit("default")@
}

}
