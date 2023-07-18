// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::pervasive_ext::string_view::*;
use crate::zookeeper_controller::{common::*, spec::zookeepercluster::*};
use vstd::prelude::*;

verus! {

pub enum ZKSupportInputView {
    ReconcileZKNode(ZookeeperClusterView),
}

pub enum ZKSupportOutputView {
    ReconcileZKNode(Result<(), Error>),
}

}
