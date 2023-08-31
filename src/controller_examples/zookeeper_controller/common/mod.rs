// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::{prelude::*, string::*};

verus! {

#[is_variant]
pub enum ZookeeperReconcileStep {
    Init,
    AfterCreateHeadlessService,
    AfterCreateClientService,
    AfterCreateAdminServerService,
    AfterGetConfigMap,
    AfterCreateConfigMap,
    AfterUpdateConfigMap,
    AfterGetStatefulSet,
    AfterExistsZKNode,
    AfterCreateZKParentNode,
    AfterCreateZKNode,
    AfterUpdateZKNode,
    AfterCreateStatefulSet,
    AfterUpdateStatefulSet,
    Done,
    Error,
}

#[is_variant]
pub enum Error {
    ZKNodeExistsFailed,
    ZKNodeCreateAlreadyExists,
    ZKNodeCreateFailed,
    ZKNodeSetDataFailed,
}

impl Error {
    pub fn is_create_already_exists(&self) -> (res: bool)
        ensures res <==> self.is_ZKNodeCreateAlreadyExists(),
    {
        match self {
            Error::ZKNodeCreateAlreadyExists => true,
            _ => false,
        }
    }
}

impl std::fmt::Debug for Error {
    #[verifier(external)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Error::ZKNodeExistsFailed => write!(f, "ZKNodeExistsFailed"),
            Error::ZKNodeCreateAlreadyExists => write!(f, "ZKNodeCreateAlreadyExists"),
            Error::ZKNodeCreateFailed => write!(f, "ZKNodeCreateFailed"),
            Error::ZKNodeSetDataFailed => write!(f, "ZKNodeSetDataFailed"),
        }
    }
}

}
