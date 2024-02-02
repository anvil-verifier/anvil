// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

// make Uid an int, instead of String, so that it is easy to compare in spec/proof
pub type Uid = int;

// make ResourceVersion an int, instead of String, so that it is easy to compare in spec/proof
pub type ResourceVersion = int;

#[is_variant]
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Kind {
    ConfigMapKind,
    CustomResourceKind,
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

impl std::marker::Copy for Kind {}

impl std::clone::Clone for Kind {
    #[verifier(external_body)]
    fn clone(&self) -> (result: Self)
        ensures result == self
    { *self }
}

pub struct ObjectRef {
    pub kind: Kind,
    pub name: StringView,
    pub namespace: StringView,
}

}
