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
    AfterCreateConfigMap,
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

}
