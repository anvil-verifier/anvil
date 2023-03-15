// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::pervasive::prelude::*;

verus! {

#[is_variant]
pub enum Kind {
    ConfigMapKind,
    CustomResourceKind,
    PersistentVolumeClaimKind,
    PodKind,
    StatefulSetKind,
    ServiceKind,
}

pub struct ObjectRef {
    pub kind: Kind,
    pub name: Seq<char>,
    pub namespace: Seq<char>,
}

}
