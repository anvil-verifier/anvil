// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{common::*, dynamic::*};
use crate::pervasive_ext::string_view::*;
use crate::zookeeper_controller::common::*;
use vstd::{prelude::*, string::*};

verus! {

pub struct ZKNodeAddr {
    pub name: StringView,
    pub namespace: StringView,
    pub uid: Uid,
    pub path: Seq<StringView>,
}

impl ZKNodeAddr {
    pub open spec fn new(name: StringView, namespace: StringView, uid: Uid, path: Seq<StringView>) -> Self {
        ZKNodeAddr {
            name: name,
            namespace: namespace,
            uid: uid,
            path: path,
        }
    }

    pub open spec fn parent_addr(self) -> Self {
        ZKNodeAddr {
            path: self.path.take(self.path.len()-1),
            ..self
        }
    }
}

pub type ZKNodeValue = StringView;

pub type ZKNodeVersion = nat;

pub struct ZKState {
    pub data: Map<ZKNodeAddr, (ZKNodeValue, ZKNodeVersion)>,
}

impl ZKState {
    pub open spec fn init() -> ZKState {
        ZKState {
            data: Map::empty(),
        }
    }
}

pub struct ZKAPIExistsResultView {
    pub res: Result<Option<ZKNodeVersion>, Error>,
}

pub struct ZKAPICreateResultView {
    pub res: Result<(), Error>,
}

pub struct ZKAPISetDataResultView {
    pub res: Result<(), Error>,
}

#[is_variant]
pub enum ZKAPIInputView {
    ExistsRequest(StringView, StringView, Seq<StringView>),
    CreateRequest(StringView, StringView, Seq<StringView>, ZKNodeValue),
    SetDataRequest(StringView, StringView, Seq<StringView>, ZKNodeValue, ZKNodeVersion),
}

#[is_variant]
pub enum ZKAPIOutputView {
    ExistsResponse(ZKAPIExistsResultView),
    CreateResponse(ZKAPICreateResultView),
    SetDataResponse(ZKAPISetDataResultView),
}

pub struct ZKAPI {}

impl ExternalAPI for ZKAPI {

    type Input = ZKAPIInputView;
    type Output = ZKAPIOutputView;
    type State = ZKState;

    open spec fn transition(input: ZKAPIInputView, resources: StoredState, state: ZKState) -> (ZKState, ZKAPIOutputView) {
        match input {
            ZKAPIInputView::ExistsRequest(name, namespace, path) => {
                let (s_prime, res) = handle_exists(name, namespace, path, resources, state);
                (s_prime, ZKAPIOutputView::ExistsResponse(res))
            },
            ZKAPIInputView::CreateRequest(name, namespace, path, data) => {
                let (s_prime, res) = handle_create(name, namespace, path, data, resources, state);
                (s_prime, ZKAPIOutputView::CreateResponse(res))
            },
            ZKAPIInputView::SetDataRequest(name, namespace, path, data, version) => {
                let (s_prime, res) = handle_set_data(name, namespace, path, data, version, resources, state);
                (s_prime, ZKAPIOutputView::SetDataResponse(res))
            },
        }
    }

    open spec fn init_state() -> ZKState {
        ZKState::init()
    }
}

// The exec version of this method sets up a connection to the zookeeper cluster,
// creates the node ("/zookeeper-operator/{name}") (if not exists),
// and sets its data to the replicas number.
// The behavior can be abstracted as writing the replicas number to an "address"
// identified by the uri of the zookeeper cluster and the node path (uri, name).
// Note that the uri is decided by name and namespace, that is,
// {name}-client.{namespace}.svc.cluster.local:2181 (here we hardcode the port to 2181).
// Assuming the exec version correctly constructs the uri, we can further simplify the "address"
// as (name, namespace). That's why the key of the map is an ObjectRef (the kind is useless here.).
//
// NOTE: we assume the parent node ("/zookeeper-operator") already exists or successfully gets created
// by the exec version so we don't model it in the spec version.
// We also omit the "CLUSTER_SIZE=" prefix since it is always written with the replicas.
//
// TODO: the result of this zk api should also depend on the cluster state, for example
// whether the client service object and the zookeeper stateful set object exist.
// Specifying such dependency would require us to pass the cluster state into this function.
//
// TODO: we should also consider the uid of the stateful set (that hosts the zookeeper cluster) inside this function.
// If the stateful set (with the same name) gets deleted and recrated,
// the controller, when connecting to the same uri, will talk to a different zookeeper cluster,
// which does not remember all the data written before.
// A potential solution is to associate the written zookeeper node with the current uid of the stateful set
// by querying the cluster state.
//
// TODO: specify version number of zookeeper node to reason about potential race between the current API call and
// the old API call from the previously crashed controller.

pub open spec fn validate(name: StringView, namespace: StringView, path: Seq<StringView>, resources: StoredState) -> bool {
    let key = ObjectRef {
        kind: Kind::StatefulSetKind,
        namespace: namespace,
        name: name,
    };
    &&& path.len() > 0
    &&& resources.dom().contains(key)
}

pub open spec fn handle_exists(
    name: StringView, namespace: StringView, path: Seq<StringView>, resources: StoredState, state: ZKState
) -> (ZKState, ZKAPIExistsResultView) {
    let key = ObjectRef { kind: Kind::StatefulSetKind, namespace: namespace, name: name };
    if !validate(name, namespace, path, resources) {
        (state, ZKAPIExistsResultView{res: Err(Error::ZKNodeExistsFailed)})
    } else {
        let current_uid = resources[key].metadata.uid.get_Some_0();
        let addr = ZKNodeAddr::new(name, namespace, current_uid, path);
        if !state.data.dom().contains(addr) {
            (state, ZKAPIExistsResultView{res: Ok(None)})
        } else {
            let version = state.data[addr].1;
            (state, ZKAPIExistsResultView{res: Ok(Some(version))})
        }
    }
}

pub open spec fn handle_create(
    name: StringView, namespace: StringView, path: Seq<StringView>, data: ZKNodeValue, resources: StoredState, state: ZKState
) -> (ZKState, ZKAPICreateResultView) {
    let key = ObjectRef { kind: Kind::StatefulSetKind, namespace: namespace, name: name };
    if !validate(name, namespace, path, resources) {
        (state, ZKAPICreateResultView{res: Err(Error::ZKNodeCreateFailed)})
    } else {
        let current_uid = resources[key].metadata.uid.get_Some_0();
        let addr = ZKNodeAddr::new(name, namespace, current_uid, path);
        if !state.data.dom().contains(addr) {
            if path.len() > 1 && !state.data.dom().contains(addr.parent_addr()) {
                (state, ZKAPICreateResultView{res: Err(Error::ZKNodeCreateFailed)})
            } else {
                let state_prime = ZKState {
                    data: state.data.insert(addr, (data, 0)),
                };
                (state_prime, ZKAPICreateResultView{res: Ok(())})
            }
        } else {
            (state, ZKAPICreateResultView{res: Err(Error::ZKNodeCreateAlreadyExists)})
        }
    }
}

pub open spec fn handle_set_data(
    name: StringView, namespace: StringView, path: Seq<StringView>, data: ZKNodeValue, version: ZKNodeVersion, resources: StoredState, state: ZKState
) -> (ZKState, ZKAPISetDataResultView) {
    let key = ObjectRef { kind: Kind::StatefulSetKind, namespace: namespace, name: name };
    if !validate(name, namespace, path, resources) {
        (state, ZKAPISetDataResultView{res: Err(Error::ZKNodeCreateFailed)})
    } else {
        let current_uid = resources[key].metadata.uid.get_Some_0();
        let addr = ZKNodeAddr::new(name, namespace, current_uid, path);
        if !state.data.dom().contains(addr) {
            (state, ZKAPISetDataResultView{res: Err(Error::ZKNodeSetDataFailed)})
        } else {
            let current_version = state.data[addr].1;
            if current_version != version {
                (state, ZKAPISetDataResultView{res: Err(Error::ZKNodeSetDataFailed)})
            } else {
                let state_prime = ZKState {
                    data: state.data.insert(addr, (data, current_version + 1)),
                };
                (state_prime, ZKAPISetDataResultView{res: Ok(())})
            }
        }
    }
}

}
