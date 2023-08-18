// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::common::*;
use crate::pervasive_ext::string_view::*;
use crate::zookeeper_controller::common::*;
use vstd::{prelude::*, string::*};

verus! {

pub struct ZKAPIResultView {
    pub res: Result<(), Error>,
}

#[is_variant]
pub enum ZKAPIInputView {
    SetZKNodeRequest(StringView, StringView, StringView),
}

#[is_variant]
pub enum ZKAPIOutputView {
    SetZKNodeResponse(ZKAPIResultView),
}

pub struct ZooKeeperState {
    pub data: Map<ObjectRef, StringView>,
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
            ZKAPIInputView::SetZKNodeRequest(zk_name, zk_namespace, replicas) => set_zk_node(zk_name, zk_namespace, replicas, state),
        }
    }

    open spec fn init_state() -> ZooKeeperState {
        ZooKeeperState::default()
    }
}

pub open spec fn set_zk_node(
    zk_name: StringView, zk_namespace: StringView, replicas: StringView, state: ZooKeeperState
) -> (Option<ZKAPIOutputView>, ZooKeeperState) {
    // Here we assume the parent node ("/zookeeper-operator") already exists so we don't model it.
    // We also omit the "CLUSTER_SIZE=" prefix since it is always written with the replicas.
    //
    // TODO: the result of this zk api should also depend on the cluster state, for example
    // whether the client service object and the zookeeper stateful set object exist.
    // Specifying such dependency would require us to pass the cluster state (the map) into this function.
    //
    // TODO: specify version number to reason about potential race between the current API call and
    // the old API call from the previously crashed controller.
    let key = ObjectRef {
        kind: Kind::CustomResourceKind,
        namespace: zk_namespace,
        name: zk_name,
    };
    let new_data = state.data.insert(key, replicas);
    let state_prime = ZooKeeperState {
        data: new_data,
        ..state
    };
    (Some(ZKAPIOutputView::SetZKNodeResponse(ZKAPIResultView{res: Ok(())})), state_prime)
}

}
