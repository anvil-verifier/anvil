// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::common::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// OwnerReferenceView is the ghost type of OwnerReference.


pub struct OwnerReferenceView {
    pub block_owner_deletion: Option<bool>,
    pub controller: Option<bool>,
    pub kind: Kind,
    pub name: StringView,
    pub uid: Uid,
}

impl OwnerReferenceView {
    // default() isn't needed; this is just to make the macro implement_field_wrapper_type happy
    pub uninterp spec fn default() -> OwnerReferenceView;
}

pub open spec fn owner_reference_to_object_reference(owner_reference: OwnerReferenceView, namespace: StringView) -> ObjectRef {
    ObjectRef {
        kind: owner_reference.kind,
        namespace: namespace,
        name: owner_reference.name,
    }
}

pub open spec fn controller_owner_filter() -> spec_fn(OwnerReferenceView) -> bool {
    |o: OwnerReferenceView| o.controller is Some && o.controller->0
}

pub open spec fn owner_reference_eq_without_uid(r1: OwnerReferenceView, r2: OwnerReferenceView) -> bool {
    &&& r1.controller == r2.controller
    &&& r1.block_owner_deletion == r2.block_owner_deletion
    &&& r1.kind == r2.kind
    &&& r1.name == r2.name
}

}
