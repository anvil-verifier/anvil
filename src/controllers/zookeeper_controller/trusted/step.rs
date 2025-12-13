// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::{prelude::*, string::*};

verus! {

pub enum ZookeeperReconcileStep {
    Init,
    AfterKRequestStep(ActionKind, SubResource),
    AfterExistsStatefulSet,
    AfterExistsZKNode,
    AfterCreateZKParentNode,
    AfterCreateZKNode,
    AfterUpdateZKNode,
    AfterUpdateStatus,
    Done,
    Error,
}

impl std::marker::Copy for ZookeeperReconcileStep {}

impl std::clone::Clone for ZookeeperReconcileStep {
    #[verifier(external_body)]
    fn clone(&self) -> (result: Self)
        ensures result == self
    { *self }
}

pub enum ActionKind {
    Get,
    Update,
    Create,
}

pub enum SubResource {
    HeadlessService,
    ClientService,
    AdminServerService,
    ConfigMap,
    StatefulSet,
}

pub enum ZKAPIError {
    ZKNodeExistsFailed,
    ZKNodeCreateAlreadyExists,
    ZKNodeCreateFailed,
    ZKNodeSetDataFailed,
}

impl ZKAPIError {
    pub fn is_create_already_exists(&self) -> (res: bool)
        ensures res <==> self is ZKNodeCreateAlreadyExists,
    {
        match self {
            ZKAPIError::ZKNodeCreateAlreadyExists => true,
            _ => false,
        }
    }
}

#[verifier(external)]
impl std::fmt::Debug for ZKAPIError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            ZKAPIError::ZKNodeExistsFailed => write!(f, "ZKNodeExistsFailed"),
            ZKAPIError::ZKNodeCreateAlreadyExists => write!(f, "ZKNodeCreateAlreadyExists"),
            ZKAPIError::ZKNodeCreateFailed => write!(f, "ZKNodeCreateFailed"),
            ZKAPIError::ZKNodeSetDataFailed => write!(f, "ZKNodeSetDataFailed"),
        }
    }
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
