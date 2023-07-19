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
    AfterCreateStatefulSet,
    AfterUpdateStatefulSet,
    Done,
    Error,
}

pub enum Error {
    ClusterSizeZKNodeCreationFailed,
}

}
