// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
pub mod seq_lemmas;
pub mod string_map;

use crate::pervasive::prelude::*;

verus! {

pub type StringView = Seq<char>;

}
