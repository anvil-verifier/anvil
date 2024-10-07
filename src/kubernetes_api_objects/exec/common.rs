// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::common::*;
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum KindExec {
    ConfigMapKind,
    CustomResourceKind(String),
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

impl View for KindExec {
    type V = Kind;

    open spec fn view(&self) -> Self::V {
        match self {
            KindExec::ConfigMapKind => Kind::ConfigMapKind,
            KindExec::DaemonSetKind => Kind::DaemonSetKind,
            KindExec::PersistentVolumeClaimKind => Kind::PersistentVolumeClaimKind,
            KindExec::PodKind => Kind::PodKind,
            KindExec::RoleBindingKind => Kind::RoleBindingKind,
            KindExec::RoleKind => Kind::RoleKind,
            KindExec::SecretKind => Kind::SecretKind,
            KindExec::ServiceKind => Kind::ServiceKind,
            KindExec::StatefulSetKind => Kind::StatefulSetKind,
            KindExec::ServiceAccountKind => Kind::ServiceAccountKind,
            KindExec::CustomResourceKind(s) => Kind::CustomResourceKind(s@),
        }
    }
}

impl std::clone::Clone for KindExec {
    #[verifier(external_body)]
    fn clone(&self) -> (result: Self)
        ensures result == self
    {
        match self {
            KindExec::ConfigMapKind => KindExec::ConfigMapKind,
            KindExec::DaemonSetKind => KindExec::DaemonSetKind,
            KindExec::PersistentVolumeClaimKind => KindExec::PersistentVolumeClaimKind,
            KindExec::PodKind => KindExec::PodKind,
            KindExec::RoleBindingKind => KindExec::RoleBindingKind,
            KindExec::RoleKind => KindExec::RoleKind,
            KindExec::SecretKind => KindExec::SecretKind,
            KindExec::ServiceKind => KindExec::ServiceKind,
            KindExec::StatefulSetKind => KindExec::StatefulSetKind,
            KindExec::ServiceAccountKind => KindExec::ServiceAccountKind,
            KindExec::CustomResourceKind(s) => KindExec::CustomResourceKind(s.clone()),
        }
    }
}

}
