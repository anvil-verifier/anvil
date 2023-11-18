// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::fluent_controller::fluentbit::model::resource as model_resource;
use crate::fluent_controller::fluentbit::trusted::{exec_types::*, step::*};
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::vstd_ext::{string_map::StringMap, string_view::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {


pub fn make_base_labels(fb: &FluentBit) -> (labels: StringMap)
    requires fb@.well_formed(),
    ensures labels@ == model_resource::make_base_labels(fb@),
{
    let mut labels = StringMap::empty();
    labels.insert(new_strlit("app").to_string(), fb.metadata().name().unwrap());
    labels
}

pub fn make_labels(fb: &FluentBit) -> (labels: StringMap)
    requires fb@.well_formed(),
    ensures labels@ == model_resource::make_labels(fb@),
{
    let mut labels = fb.spec().labels();
    labels.extend(make_base_labels(fb));
    labels
}

pub fn make_owner_references(fb: &FluentBit) -> (owner_references: Vec<OwnerReference>)
    requires fb@.well_formed(),
    ensures owner_references@.map_values(|or: OwnerReference| or@) ==  model_resource::make_owner_references(fb@),
{
    let mut owner_references = Vec::new();
    owner_references.push(fb.controller_owner_ref());
    proof {
        assert_seqs_equal!(
            owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
            model_resource::make_owner_references(fb@)
        );
    }
    owner_references
}

}
