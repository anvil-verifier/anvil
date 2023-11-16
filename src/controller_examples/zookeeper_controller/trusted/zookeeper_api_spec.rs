// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    common::*, config_map::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::vstd_ext::string_view::*;
use crate::zookeeper_controller::trusted::{
    config_map::*, spec_types::ZookeeperClusterView, step::*,
};
use vstd::{prelude::*, string::*};

verus! {

// ZKNodeAddr represents the location of a zk node.
// Here the location includes not only the key (i.e., the path field),
// but also the zookeeper cluster (hosted by some stateful set object).
// The zookeeper cluster is identified by name, namespace and uid:
// the name and namespace tells which stateful set object hosts the zookeeper cluster
// (and gives us the uri to connect to), and the uid helps to distinguish stateful set
// objects that share the same name -- the new stateful set object shares the same name/namespace,
// but does not inherit the data stored in the previous zookeeper cluster.
//
// Note that the path is represented as a sequence of string(view), because zookeeper exposes
// a file system like interface to the user: each node is a file path with some data associated with it,
// and each node can have child and parent node just like a hierarchical file system.
// We use the sequence to represent the full path for each node.
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

pub struct ZKAPI {}

pub type ZKNodeValue = StringView;

pub type ZKNodeVersion = int;

// ZKState is basically a map from the key (the id of the zookeeper cluster and the node path)
// to the value, and the stat data associated with the node (i.e., version number).
pub struct ZKState {
    pub data: Map<ZKNodeAddr, (ZKNodeValue, ZKNodeVersion)>,
}

impl ZKState {
    pub open spec fn init() -> ZKState { ZKState { data: Map::empty() } }
}

pub struct ZKAPIExistsResultView {
    pub res: Result<Option<ZKNodeVersion>, ZKAPIError>,
}

pub struct ZKAPICreateResultView {
    pub res: Result<(), ZKAPIError>,
}

pub struct ZKAPISetDataResultView {
    pub res: Result<(), ZKAPIError>,
}

#[is_variant]
pub enum ZKAPIInputView {
    ExistsRequest(StringView, StringView, int, Seq<StringView>),
    CreateRequest(StringView, StringView, int, Seq<StringView>, ZKNodeValue),
    SetDataRequest(StringView, StringView, int, Seq<StringView>, ZKNodeValue, ZKNodeVersion),
}

#[is_variant]
pub enum ZKAPIOutputView {
    ExistsResponse(ZKAPIExistsResultView),
    CreateResponse(ZKAPICreateResultView),
    SetDataResponse(ZKAPISetDataResultView),
}

impl ExternalAPI for ZKAPI {

    type Input = ZKAPIInputView;
    type Output = ZKAPIOutputView;
    type State = ZKState;

    open spec fn transition(input: ZKAPIInputView, resources: StoredState, state: ZKState) -> (ZKState, ZKAPIOutputView) {
        match input {
            ZKAPIInputView::ExistsRequest(name, namespace, port, path) => {
                let (s_prime, res) = handle_exists(name, namespace, port, path, resources, state);
                (s_prime, ZKAPIOutputView::ExistsResponse(res))
            },
            ZKAPIInputView::CreateRequest(name, namespace, port, path, data) => {
                let (s_prime, res) = handle_create(name, namespace, port, path, data, resources, state);
                (s_prime, ZKAPIOutputView::CreateResponse(res))
            },
            ZKAPIInputView::SetDataRequest(name, namespace, port, path, data, version) => {
                let (s_prime, res) = handle_set_data(name, namespace, port, path, data, version, resources, state);
                (s_prime, ZKAPIOutputView::SetDataResponse(res))
            },
        }
    }

    open spec fn init_state() -> ZKState { ZKState::init() }
}

pub open spec fn validate_config_map_data(data: Map<StringView, StringView>) -> bool {
    let zk_config = data[new_strlit("zoo.cfg")@];
    &&& data.contains_key(new_strlit("zoo.cfg")@)
    &&& exists |zk: ZookeeperClusterView| zk.state_validation() && (#[trigger] make_zk_config(zk)) == zk_config
}

pub open spec fn validate_config_map_object(object: DynamicObjectView) -> bool {
    &&& ConfigMapView::unmarshal(object).is_Ok()
    &&& ConfigMapView::unmarshal(object).get_Ok_0().data.is_Some()
    &&& validate_config_map_data(ConfigMapView::unmarshal(object).get_Ok_0().data.get_Some_0())
}

pub open spec fn validate_config_map(name: StringView, namespace: StringView, resources: StoredState) -> bool {
    let cm_key = ObjectRef {
        kind: Kind::ConfigMapKind,
        namespace: namespace,
        name: name + new_strlit("-configmap")@,
    };
    &&& resources.contains_key(cm_key)
    &&& validate_config_map_object(resources[cm_key])
}

pub open spec fn validate_stateful_set(name: StringView, namespace: StringView, resources: StoredState) -> bool {
    let sts_key = ObjectRef {
        kind: Kind::StatefulSetKind,
        namespace: namespace,
        name: name,
    };
    let sts_spec = StatefulSetView::unmarshal(resources[sts_key]).get_Ok_0().spec;
    // The stateful set object exists
    &&& resources.contains_key(sts_key)
    &&& StatefulSetView::unmarshal(resources[sts_key]).is_Ok()
    &&& sts_spec.is_Some()
    &&& sts_spec.get_Some_0().replicas.is_Some()
    // and it has at least one replica to handle the request
    &&& sts_spec.get_Some_0().replicas.get_Some_0() > 0
}

// validate checks the stateful set object (the end point that the client connects to in the exec implementation)
// exists, and the path is valid.
//
// TODO: more validation check could be implemented,
// such as checking the existence of the service object as well,
// checking whether the stateful set is really ready,
// and checking whether the port number is correct.
pub open spec fn validate(name: StringView, namespace: StringView, port: int, path: Seq<StringView>, resources: StoredState) -> bool {
    &&& path.len() > 0
    &&& validate_stateful_set(name, namespace, resources)
    &&& validate_config_map(name, namespace, resources)
}

// handle_exists models the behavior of the zookeeper server handling the exists request.
// It checks the existence of the node by querying the map.
// If the node exists, it returns its stat (i.e., version number), otherwise none.
// Note that it uses the uid to avoid querying the data belonging to the old stateful set object.
pub open spec fn handle_exists(name: StringView, namespace: StringView, port: int, path: Seq<StringView>, resources: StoredState, state: ZKState) -> (ZKState, ZKAPIExistsResultView) {
    let key = ObjectRef { kind: Kind::StatefulSetKind, namespace: namespace, name: name };
    if !validate(name, namespace, port, path, resources) {
        (state, ZKAPIExistsResultView{res: Err(ZKAPIError::ZKNodeExistsFailed)})
    } else {
        let addr = ZKNodeAddr::new(name, namespace, resources[key].metadata.uid.get_Some_0(), path);
        if !state.data.contains_key(addr) {
            (state, ZKAPIExistsResultView{res: Ok(None)})
        } else {
            let version = state.data[addr].1;
            (state, ZKAPIExistsResultView{res: Ok(Some(version))})
        }
    }
}

// handle_create models the behavior of the zookeeper server handling the create request.
// The creation succeeds only when (1) the node does not exist yet and (2) the parent node exists.
pub open spec fn handle_create(name: StringView, namespace: StringView, port: int, path: Seq<StringView>, data: ZKNodeValue, resources: StoredState, state: ZKState) -> (ZKState, ZKAPICreateResultView) {
    let key = ObjectRef { kind: Kind::StatefulSetKind, namespace: namespace, name: name };
    if !validate(name, namespace, port, path, resources) {
        (state, ZKAPICreateResultView{res: Err(ZKAPIError::ZKNodeCreateFailed)})
    } else {
        let addr = ZKNodeAddr::new(name, namespace, resources[key].metadata.uid.get_Some_0(), path);
        if !state.data.contains_key(addr) {
            if path.len() > 1 && !state.data.contains_key(addr.parent_addr()) {
                (state, ZKAPICreateResultView{res: Err(ZKAPIError::ZKNodeCreateFailed)})
            } else {
                let state_prime = ZKState { data: state.data.insert(addr, (data, 0)) };
                (state_prime, ZKAPICreateResultView{res: Ok(())})
            }
        } else {
            (state, ZKAPICreateResultView{res: Err(ZKAPIError::ZKNodeCreateAlreadyExists)})
        }
    }
}

// handle_set_data models the behavior of the zookeeper server handling the set data request.
// To set the data, the node needs to exist and the provided version number must match the current version of the node.
pub open spec fn handle_set_data(name: StringView, namespace: StringView, port: int, path: Seq<StringView>, data: ZKNodeValue, version: ZKNodeVersion, resources: StoredState, state: ZKState) -> (ZKState, ZKAPISetDataResultView) {
    let key = ObjectRef { kind: Kind::StatefulSetKind, namespace: namespace, name: name };
    if !validate(name, namespace, port, path, resources) {
        (state, ZKAPISetDataResultView{res: Err(ZKAPIError::ZKNodeSetDataFailed)})
    } else {
        let addr = ZKNodeAddr::new(name, namespace, resources[key].metadata.uid.get_Some_0(), path);
        if !state.data.contains_key(addr) {
            (state, ZKAPISetDataResultView{res: Err(ZKAPIError::ZKNodeSetDataFailed)})
        } else {
            let current_version = state.data[addr].1;
            if current_version != version {
                (state, ZKAPISetDataResultView{res: Err(ZKAPIError::ZKNodeSetDataFailed)})
            } else {
                let state_prime = ZKState { data: state.data.insert(addr, (data, current_version + 1)) };
                (state_prime, ZKAPISetDataResultView{res: Ok(())})
            }
        }
    }
}

}
