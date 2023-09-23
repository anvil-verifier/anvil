// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

#[is_variant]
pub enum RabbitmqReconcileStep {
    Init,
    AfterKRequestStep(ActionKind, ResourceKind),
    Done,
    Error,
}

impl std::marker::Copy for RabbitmqReconcileStep {}

impl std::clone::Clone for RabbitmqReconcileStep {
    fn clone(&self) -> Self {
        *self
    }
}

pub enum ResourceKind {
    HeadlessService,
    Service,
    ErlangCookieSecret,
    DefaultUserSecret,
    PluginsConfigMap,
    ServerConfigMap,
    ServiceAccount,
    Role,
    RoleBinding,
    StatefulSet,
}

#[is_variant]
pub enum ActionKind {
    Get,
    Create,
    Update,
}

impl std::marker::Copy for ResourceKind {}

impl std::clone::Clone for ResourceKind {
    fn clone(&self) -> Self {
        *self
    }
}

impl std::marker::Copy for ActionKind {}

impl std::clone::Clone for ActionKind {
    fn clone(&self) -> Self {
        *self
    }
}

#[is_variant]
pub enum RabbitmqError {
    Error
}

impl std::fmt::Debug for RabbitmqError {
    #[verifier(external)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            RabbitmqError::Error => write!(f, "Error"),
        }
    }
}

pub open spec fn resource_res_to_view<T: View>(res: Result<T, RabbitmqError>) -> Result<T::V, RabbitmqError> {
    match res {
        Ok(resource) => Ok(resource@),
        Err(err) => Err(err),
    }
}

}
