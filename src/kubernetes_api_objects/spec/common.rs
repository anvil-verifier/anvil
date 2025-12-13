// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// make Uid an int, instead of String, so that it is easy to compare in spec/proof
pub type Uid = int;

// make ResourceVersion an int, instead of String, so that it is easy to compare in spec/proof
pub type ResourceVersion = int;

// GenerateNameCounter is used to specify how the API server generates a random and unique name
// according to the generate name field
// make GenerateNameCounter an int, instead of String, so that it is easy to compare in spec/proof
pub type GenerateNameCounter = int;

pub enum Kind {
    ConfigMapKind,
    CustomResourceKind(StringView),
    DaemonSetKind,
    PersistentVolumeClaimKind,
    PodKind,
    RoleKind,
    RoleBindingKind,
    StatefulSetKind,
    ServiceKind,
    ServiceAccountKind,
    SecretKind,
}

pub struct ObjectRef {
    pub kind: Kind,
    pub name: StringView,
    pub namespace: StringView,
}

}
