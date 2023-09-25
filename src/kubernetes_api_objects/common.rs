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
pub enum Kind {
    ConfigMapKind,
    CustomResourceKind,
    ClusterRoleKind,
    ClusterRoleBindingKind,
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
