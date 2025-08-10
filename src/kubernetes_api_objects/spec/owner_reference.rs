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

}
