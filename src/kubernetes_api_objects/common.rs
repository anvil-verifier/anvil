// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

#[is_variant]
pub enum Kind {
    ConfigMapKind,
    CustomResourceKind,
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

pub struct KubeObjectRef {
    pub kind: Kind,
    pub name: String,
    pub namespace: String,
}

impl KubeObjectRef {
    pub open spec fn to_view(&self) -> ObjectRef {
        ObjectRef {
            kind: self.kind,
            name: self.name@,
            namespace: self.namespace@,
        }
    }
}

}
