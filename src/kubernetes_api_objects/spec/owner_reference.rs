// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{common::*, marshal::*, resource::*};
use crate::vstd_ext::string_map::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

/// OwnerReferenceView is the ghost type of OwnerReference.
/// It is supposed to be used in spec and proof code.

pub struct OwnerReferenceView {
    pub block_owner_deletion: Option<bool>,
    pub controller: Option<bool>,
    pub kind: Kind,
    pub name: StringView,
    pub uid: Uid,
}

impl OwnerReferenceView {
    pub open spec fn is_controller_ref(self) -> bool {
        self.controller.is_Some()
        && self.controller.get_Some_0()
    }
}

pub open spec fn owner_reference_to_object_reference(owner_reference: OwnerReferenceView, namespace: StringView) -> ObjectRef {
    ObjectRef {
        kind: owner_reference.kind,
        namespace: namespace,
        name: owner_reference.name,
    }
}

}
