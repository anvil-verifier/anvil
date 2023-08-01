// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::pervasive_ext::string_view::*;
use crate::zookeeper_controller::{common::*, spec::zookeepercluster::*};
use vstd::{prelude::*, string::*};

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

pub struct ZooKeeperState {
    pub data: Map<StringView, StringView>,
}

pub open spec fn external_process(input: ZKSupportInputView, state: Option<ZooKeeperState>) -> (Option<ZKSupportOutputView>, Option<ZooKeeperState>) {
    match input {
        ZKSupportInputView::ReconcileZKNode(path,uri,replicas) => reconcile_zk_node(path, uri, replicas, state),
    }
}

pub open spec fn reconcile_zk_node(
    path: StringView, uri: StringView, replicas: StringView, state: Option<ZooKeeperState>
) -> (Option<ZKSupportOutputView>, Option<ZooKeeperState>) {
    let old_state = if state.is_None() { ZooKeeperState{ data: Map::empty() } } else { state.get_Some_0() };
    if old_state.data.contains_key(uri + path) {
        let state_prime = ZooKeeperState {
            data: old_state.data.insert(uri + path, new_strlit("CLUSTER_SIZE=")@ + replicas),
            ..old_state
        };
        (Option::Some(ZKSupportOutputView::ReconcileZKNode(ZKNodeResultView{ res: Ok(()) })), Option::Some(state_prime))
    } else {
        let new_data = old_state.data
                    .insert(uri + new_strlit("/zookeeper-operator")@, new_strlit("")@)
                    .insert(uri + path, new_strlit("CLUSTER_SIZE=")@ + replicas);
        let state_prime = ZooKeeperState {
            data: new_data,
            ..old_state
        };
        (Option::Some(ZKSupportOutputView::ReconcileZKNode(ZKNodeResultView{ res: Ok(()) })), Option::Some(state_prime))
    }
}

}
