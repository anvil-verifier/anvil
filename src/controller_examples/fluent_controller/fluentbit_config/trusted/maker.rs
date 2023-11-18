// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::fluent_controller::fluentbit_config::trusted::spec_types::FluentBitConfigView;
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::vstd_ext::{string_map::*, string_view::*};
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

pub trait Maker {
    spec fn make_secret_key(fbc: FluentBitConfigView) -> ObjectRef;

    spec fn make_secret(fbc: FluentBitConfigView) -> SecretView;
}

}