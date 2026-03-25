// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;
use crate::vstatefulset_controller::trusted::spec_types::VStatefulSetView;

verus! {

pub enum RabbitmqReconcileStep {
    Init,
    AfterKRequestStep(ActionKind, SubResource),
    Done,
    Error,
}

impl std::marker::Copy for RabbitmqReconcileStep {}

impl std::clone::Clone for RabbitmqReconcileStep {
    #[verifier(external_body)]
    fn clone(&self) -> (result: Self)
        ensures result == self
    { *self }
}

pub enum SubResource {
    HeadlessService,
    Service,
    ErlangCookieSecret,
    DefaultUserSecret,
    PluginsConfigMap,
    ServerConfigMap,
    ServiceAccount,
    Role,
    RoleBinding,
    VStatefulSetView,
}

pub enum ActionKind {
    Get,
    Create,
    Update,
}

impl std::marker::Copy for SubResource {}

impl std::clone::Clone for SubResource {
    #[verifier(external_body)]
    fn clone(&self) -> (result: Self)
        ensures result == self
    { *self }
}

impl std::marker::Copy for ActionKind {}

impl std::clone::Clone for ActionKind {
    #[verifier(external_body)]
    fn clone(&self) -> (result: Self)
        ensures result == self
    { *self }
}

}
