// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::fluent_controller::fluentbit::trusted::{spec_types::*, step::*};
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub open spec fn make_base_labels(fb: FluentBitView) -> Map<StringView, StringView> { map![new_strlit("app")@ => fb.metadata.name.get_Some_0()] }

pub open spec fn make_labels(fb: FluentBitView) -> Map<StringView, StringView> { fb.spec.labels.union_prefer_right(make_base_labels(fb)) }

pub open spec fn make_owner_references(fb: FluentBitView) -> Seq<OwnerReferenceView> { seq![fb.controller_owner_ref()] }

}
