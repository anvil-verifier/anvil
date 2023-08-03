// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::spec::*;
use crate::pervasive_ext::string_view::*;
use crate::zookeeper_controller::{common::*, spec::zookeepercluster::*};
use vstd::{prelude::*, string::*};

verus! {

#[is_variant]
pub enum ZKAPIInputView {
    ReconcileZKNode(StringView,StringView,StringView),
}

#[is_variant]
pub enum ZKAPIOutputView {
    ReconcileZKNode(ZKNodeResultView),
}

pub struct ZKNodeResultView {
    pub res: Result<(), Error>,
}

pub struct ZooKeeperState {
    pub data: Map<StringView, StringView>,
}

impl ZooKeeperState {
    pub open spec fn default() -> ZooKeeperState {
        ZooKeeperState {
            data: Map::empty(),
        }
    }
}

pub struct ZKAPI {}

impl ExternalAPI for ZKAPI {

    type Input = ZKAPIInputView;
    type Output = ZKAPIOutputView;
    type State = ZooKeeperState;

    open spec fn transition(input: ZKAPIInputView, state: ZooKeeperState) -> (Option<ZKAPIOutputView>, ZooKeeperState) {
        match input {
            ZKAPIInputView::ReconcileZKNode(path,uri,replicas) => reconcile_zk_node(path, uri, replicas, state),
        }
    }

    open spec fn init_state() -> ZooKeeperState {
        ZooKeeperState::default()
    }
}

pub open spec fn reconcile_zk_node(
    path: StringView, uri: StringView, replicas: StringView, state: ZooKeeperState
) -> (Option<ZKAPIOutputView>, ZooKeeperState) {
    if state.data.contains_key(uri + path) {
        let state_prime = ZooKeeperState {
            data: state.data.insert(uri + path, new_strlit("CLUSTER_SIZE=")@ + replicas),
            ..state
        };
        (Option::Some(ZKAPIOutputView::ReconcileZKNode(ZKNodeResultView{ res: Ok(()) })), state_prime)
    } else {
        let new_data = state.data
                    .insert(uri + new_strlit("/zookeeper-operator")@, new_strlit("")@)
                    .insert(uri + path, new_strlit("CLUSTER_SIZE=")@ + replicas);
        let state_prime = ZooKeeperState {
            data: new_data,
            ..state
        };
        (Option::Some(ZKAPIOutputView::ReconcileZKNode(ZKNodeResultView{ res: Ok(()) })), state_prime)
    }
}

}
