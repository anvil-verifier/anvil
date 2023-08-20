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

// The exec version of this method sets up a connection to the zookeeper cluster,
// creates the node ("/zookeeper-operator/{zk_name}") (if not exists),
// and sets its data to the replicas number.
// The behavior can be abstracted as writing the replicas number to an "address"
// identified by the uri of the zookeeper cluster and the node path (uri, zk_name).
// Note that the uri is decided by zk_name and zk_namespace, that is,
// {zk_name}-client.{zk_namespace}.svc.cluster.local:2181 (here we hardcode the port to 2181).
// Assuming the exec version correctly constructs the uri, we can further simplify the "address"
// as (zk_name, zk_namespace). That's why the key of the map is an ObjectRef (the kind is useless here.).
//
// NOTE: we assume the parent node ("/zookeeper-operator") already exists or successfully gets created
// by the exec version so we don't model it in the spec version.
// We also omit the "CLUSTER_SIZE=" prefix since it is always written with the replicas.
//
// TODO: the address should probably also include the uid of the stateful set.
// If the stateful set (with the same name) gets deleted and recrated,
// the controller, when connecting to the same uri, essentially talks to a different zookeeper cluster.
// Using uid in the address can help to distinguish different zookeeper clusters (with the same name).
//
// TODO: the result of this zk api should also depend on the cluster state, for example
// whether the client service object and the zookeeper stateful set object exist.
// Specifying such dependency would require us to pass the cluster state into this function.
//
// TODO: specify version number of zookeeper node to reason about potential race between the current API call and
// the old API call from the previously crashed controller.
pub open spec fn set_zk_node(
    zk_name: StringView, zk_namespace: StringView, replicas: StringView, state: ZooKeeperState
) -> (Option<ZKAPIOutputView>, ZooKeeperState) {
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
