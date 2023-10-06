// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::fluent_controller::fluentbit_config::common::*;
use crate::fluent_controller::fluentbit_config::exec::types::*;
use crate::fluent_controller::fluentbit_config::spec::resource as spec_resource;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::vstd_ext::{string_map::StringMap, string_view::*, to_view::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub fn make_owner_references(fbc: &FluentBitConfig) -> (owner_references: Vec<OwnerReference>)
    requires
        fbc@.well_formed(),
    ensures
        owner_references@.map_values(|or: OwnerReference| or@) ==  spec_resource::make_owner_references(fbc@),
{
    let mut owner_references = Vec::new();
    owner_references.push(fbc.controller_owner_ref());
    proof {
        assert_seqs_equal!(
            owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
            spec_resource::make_owner_references(fbc@)
        );
    }
    owner_references
}

}
