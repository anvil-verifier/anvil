// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::{prelude::*, string::*};

verus! {

#[is_variant]
pub enum ZookeeperReconcileStep {
    Init,
    AfterGetHeadlessService,
    AfterCreateHeadlessService,
    AfterUpdateHeadlessService,
    AfterGetClientService,
    AfterCreateClientService,
    AfterUpdateClientService,
    AfterGetAdminServerService,
    AfterCreateAdminServerService,
    AfterUpdateAdminServerService,
    AfterGetConfigMap,
    AfterCreateConfigMap,
    AfterUpdateConfigMap,
    AfterGetStatefulSet,
    AfterExistsZKNode,
    AfterCreateZKParentNode,
    AfterCreateZKNode,
    AfterUpdateZKNode,
    AfterGetStatefulSet2,
    AfterCreateStatefulSet,
    AfterUpdateStatefulSet,
    Done,
    Error,
}

#[is_variant]
pub enum ZKAPIError {
    ZKNodeExistsFailed,
    ZKNodeCreateAlreadyExists,
    ZKNodeCreateFailed,
    ZKNodeSetDataFailed,
}

impl ZKAPIError {
    pub fn is_create_already_exists(&self) -> (res: bool)
        ensures res <==> self.is_ZKNodeCreateAlreadyExists(),
    {
        match self {
            ZKAPIError::ZKNodeCreateAlreadyExists => true,
            _ => false,
        }
    }
}

impl std::fmt::Debug for ZKAPIError {
    #[verifier(external)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            ZKAPIError::ZKNodeExistsFailed => write!(f, "ZKNodeExistsFailed"),
            ZKAPIError::ZKNodeCreateAlreadyExists => write!(f, "ZKNodeCreateAlreadyExists"),
            ZKAPIError::ZKNodeCreateFailed => write!(f, "ZKNodeCreateFailed"),
            ZKAPIError::ZKNodeSetDataFailed => write!(f, "ZKNodeSetDataFailed"),
        }
    }
}

}
