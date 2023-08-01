// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::pervasive_ext::string_view::*;
use crate::zookeeper_controller::{common::*, spec::zookeepercluster::*};
use vstd::prelude::*;

verus! {

#[is_variant]
pub enum ZKSupportInputView {
    ReconcileZKNode(StringView,StringView,StringView),
}

#[is_variant]
pub enum ZKSupportOutputView {
    ReconcileZKNode(ZKNodeResultView),
}

pub struct ZKNodeResultView {
    pub res: Result<(), Error>,
}

pub struct ZooKeeperState {}

// pub open spec external_process(input: ZKSupportInputView, state: ZooKeeperState) -> (Option<ZKSupportOutputView>, ZooKeeperState> {

// }

}
