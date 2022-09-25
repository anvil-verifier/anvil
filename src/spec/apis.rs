// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#[allow(unused_imports)]
use crate::common::*;
#[allow(unused_imports)]
use crate::custom_controller_var::*;
#[allow(unused_imports)]
use crate::dict::*;
#[allow(unused_imports)]
use crate::pervasive::{map::Map, option::Option, *};
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

#[derive(Structural, PartialEq, Eq)]
pub enum ReconcileStep {
    Init,
    CustomReconcileStep(CustomReconcileStep), // The argument is defined by the controller developer
    Retry,
    Done,
}

#[derive(PartialEq, Eq)]
pub struct MetadataL {
    pub name: StringL,
    pub namespace: StringL,
    pub owner_key: ObjectKey, // TODO: replace this with owner_references
}

#[derive(PartialEq, Eq)]
pub struct PodL {
    pub metadata: MetadataL,
}

impl PodL {
    pub open spec fn key(&self) -> ObjectKey {
        ObjectKey{
            object_type: StringL::Pod,
            namespace: self.metadata.namespace,
            name: self.metadata.name,
        }
    }
}

#[derive(PartialEq, Eq)]
pub struct ConfigMapL {
    pub metadata: MetadataL,
}

impl ConfigMapL {
    pub open spec fn key(&self) -> ObjectKey {
        ObjectKey{
            object_type: StringL::ConfigMap,
            namespace: self.metadata.namespace,
            name: self.metadata.name,
        }
    }
}

#[derive(PartialEq, Eq)]
pub enum KubernetesObject {
    None,
    Pod(PodL),
    ConfigMap(ConfigMapL),
    CustomResourceObject(CustomResourceObject),
}

impl KubernetesObject {
    pub open spec fn matches(&self, key:ObjectKey) -> bool {
        match *self {
            KubernetesObject::Pod(p) => key === p.key(),
            KubernetesObject::ConfigMap(cm) => key === cm.key(),
            KubernetesObject::CustomResourceObject(cro) => key === cro.key(),
            KubernetesObject::None => false,
        }
    }
}

pub struct ClusterStateImpl {
    pub state: Dict<ObjectKey, KubernetesObject>
}

pub struct ClusterState {
    pub state: Map<ObjectKey, KubernetesObject>
}

impl ClusterState {
    pub open spec fn empty(&self) -> bool {
        equal(self.state, Map::empty())
    }

    pub open spec fn get(&self, object_key:ObjectKey) -> KubernetesObject {
        if self.state.dom().contains(object_key) {
            self.state.index(object_key)
        } else {
            KubernetesObject::None
        }
    }

    pub open spec fn contains(&self, object_key:ObjectKey) -> bool {
        self.state.dom().contains(object_key)
    }

    pub open spec fn len(&self) -> nat {
        self.state.dom().len()
    }

    pub open spec fn well_formed(&self) -> bool {
        forall |key:ObjectKey| #[trigger] self.state.dom().contains(key) ==> self.state.index(key).matches(key)
    }
}

#[derive(PartialEq, Eq)]
pub enum APIOp {
    Get{object_key: ObjectKey},
    Create{object_key: ObjectKey, object:KubernetesObject},
    Update{object_key: ObjectKey, object:KubernetesObject},
    Delete{object_key: ObjectKey},
}

impl APIOp {
    pub open spec fn well_formed(&self) -> bool {
        match *self {
            APIOp::Create{object_key, object} => object.matches(object_key),
            APIOp::Update{object_key, object} => object.matches(object_key),
            _ => true,
        }
    }
}

pub struct APIOpRequest {
    pub api_op: APIOp
}

impl APIOpRequest {
    pub open spec fn well_formed(&self) -> bool {
        self.api_op.well_formed()
    }

    pub open spec fn key(&self) -> ObjectKey {
        match self.api_op {
            APIOp::Get{object_key} => object_key,
            APIOp::Create{object_key, ..} => object_key,
            APIOp::Update{object_key, ..} => object_key,
            APIOp::Delete{object_key} => object_key,
        }
    }
}

pub struct APIOpResponse {
    pub success: bool,
    pub api_op_request: APIOpRequest,
    pub optional_object: Option<KubernetesObject>,
    // should also return the error type if any
}

impl APIOpResponse {
    pub open spec fn well_formed(&self) -> bool {
        self.api_op_request.well_formed()
        // TODO: revisit this branch
        && (!self.success ==> self.optional_object.is_None())
        && (self.success ==> self.optional_object.is_Some()
            && match self.api_op_request.api_op {
                APIOp::Get{object_key} => self.optional_object.get_Some_0().matches(object_key),
                APIOp::Create{object_key, ..} => self.optional_object.get_Some_0().matches(object_key),
                APIOp::Update{object_key, ..} => self.optional_object.get_Some_0().matches(object_key),
                APIOp::Delete{object_key} => self.optional_object.get_Some_0().matches(object_key),
            }
        )
    }

    pub open spec fn key(&self) -> ObjectKey {
        match self.api_op_request.api_op {
            APIOp::Get{object_key} => object_key,
            APIOp::Create{object_key, ..} => object_key,
            APIOp::Update{object_key, ..} => object_key,
            APIOp::Delete{object_key} => object_key,
        }
    }
}

pub enum WatchDeltaType {
    Create,
    Update,
    Delete,
}

pub struct APIWatchNotification {
    pub object: KubernetesObject,
    pub delta_type: WatchDeltaType
}

impl APIWatchNotification {
    pub open spec fn well_formed(&self) -> bool {
        true
    }

    // TODO: implement a key function
}

pub enum Message {
    APIOpRequest(APIOpRequest),
    APIOpResponse(APIOpResponse),
    APIWatchNotification(APIWatchNotification),
}

impl Message {
    pub open spec fn well_formed(&self) -> bool {
        match *self {
            Message::APIOpRequest(api_op_request) => api_op_request.well_formed(),
            Message::APIOpResponse(api_op_response) => api_op_response.well_formed(),
            Message::APIWatchNotification(api_watch_notification) => api_watch_notification.well_formed(),
        }
    }
}

pub enum HostId {
    KubernetesAPI,
    CustomController,
    CustomClient,
}

pub struct Packet {
    pub src: HostId,
    pub dst: HostId,
    pub message: Message,
}

impl Packet {
    pub open spec fn well_formed(&self) -> bool {
        self.message.well_formed()
    }
}

pub struct NetworkOps {
    pub recv: Option<Packet>,
    pub send: Option<Packet>,
}

impl NetworkOps {
    pub open spec fn recv_well_formed(&self) -> bool {
        match self.recv {
            Option::None => true,
            Option::Some(packet) => packet.well_formed(),
        }
    }

    pub open spec fn send_well_formed(&self) -> bool {
        match self.send {
            Option::None => true,
            Option::Some(packet) => packet.well_formed(),
        }
    }

    pub open spec fn well_formed(&self) -> bool {
        self.recv_well_formed()
        && self.send_well_formed()
    }
}

pub open spec fn state_transition_by_api_op(cluster_state: ClusterState, cluster_state_prime: ClusterState, api_op: APIOp) -> bool {
    match api_op {
        APIOp::Get{object_key} => cluster_state.contains(object_key) && equal(cluster_state, cluster_state_prime),
        APIOp::Create{object_key, object} => !cluster_state.contains(object_key) && equal(cluster_state.state.insert(object_key, object), cluster_state_prime.state),
        APIOp::Update{object_key, object} => cluster_state.contains(object_key) && equal(cluster_state.state.insert(object_key, object), cluster_state_prime.state),
        APIOp::Delete{object_key} => cluster_state.contains(object_key) && equal(cluster_state.state.remove(object_key), cluster_state_prime.state),
    }
}

}
