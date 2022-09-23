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
pub struct PodL {
    pub name: StringL,
    pub namespace: StringL,
}

impl PodL {
    #[spec] #[verifier(publish)]
    pub fn matches(&self, key:ObjectKey) -> bool {
        equal(key.object_type, StringL::Pod)
        && equal(key.name, self.name)
        && equal(key.namespace, self.namespace)
    }
}

#[derive(PartialEq, Eq)]
pub struct ConfigMapL {
    pub name: StringL,
    pub namespace: StringL,
    pub owner_key: ObjectKey, // TODO: replace this with owner_references
}

impl ConfigMapL {
    #[spec] #[verifier(publish)]
    pub fn matches(&self, key:ObjectKey) -> bool {
        equal(key.object_type, StringL::ConfigMap)
        && equal(key.name, self.name)
        && equal(key.namespace, self.namespace)
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
    #[spec] #[verifier(publish)]
    pub fn matches(&self, key:ObjectKey) -> bool {
        match *self {
            KubernetesObject::Pod(p) => p.matches(key),
            KubernetesObject::ConfigMap(cm) => cm.matches(key),
            KubernetesObject::CustomResourceObject(cro) => cro.matches(key),
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
    #[spec] #[verifier(publish)]
    pub fn empty(&self) -> bool {
        equal(self.state, Map::empty())
    }

    #[spec] #[verifier(publish)]
    pub fn get(&self, object_key:ObjectKey) -> KubernetesObject {
        if self.state.dom().contains(object_key) {
            self.state.index(object_key)
        } else {
            KubernetesObject::None
        }
    }

    #[spec] #[verifier(publish)]
    pub fn contains(&self, object_key:ObjectKey) -> bool {
        self.state.dom().contains(object_key)
    }

    #[spec] #[verifier(publish)]
    pub fn len(&self) -> nat {
        self.state.dom().len()
    }

    #[spec] #[verifier(publish)]
    pub fn well_formed(&self) -> bool {
        forall |key:ObjectKey| #[trigger] self.state.dom().contains(key) ==> self.state.index(key).matches(key)
    }
}

#[derive(PartialEq, Eq)]
pub enum APIOp {
    Noop,
    Get{object_key: ObjectKey},
    Create{object_key: ObjectKey, object:KubernetesObject},
    Update{object_key: ObjectKey, object:KubernetesObject},
    Delete{object_key: ObjectKey},
}

impl APIOp {
    #[spec] #[verifier(publish)]
    pub fn well_formed(&self) -> bool {
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
    #[spec] #[verifier(publish)]
    pub fn well_formed(&self) -> bool {
        self.api_op.well_formed()
    }
}

pub struct APIOpResponse {
    pub success: bool,
    pub api_op: APIOp,
    pub object: KubernetesObject,
    // should also return the error type if any
}

impl APIOpResponse {
    #[spec] #[verifier(publish)]
    pub fn well_formed(&self) -> bool {
        self.api_op.well_formed()
        && (!self.success ==> equal(self.object, KubernetesObject::None))
        && (self.success ==> match self.api_op {
            APIOp::Get{object_key} => self.object.matches(object_key),
            APIOp::Create{object_key, ..} => self.object.matches(object_key),
            APIOp::Update{object_key, ..} => self.object.matches(object_key),
            APIOp::Delete{object_key} => self.object.matches(object_key),
            _ => true,
        })
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
    #[spec] #[verifier(publish)]
    pub fn well_formed(&self) -> bool {
        true
    }
}

pub enum Message {
    APIOpRequest(APIOpRequest),
    APIOpResponse(APIOpResponse),
    APIWatchNotification(APIWatchNotification),
    WorkloadSubmission(APIOpRequest),
    // need more message types
}

impl Message {
    #[spec] #[verifier(publish)]
    pub fn well_formed(&self) -> bool {
        match *self {
            Message::APIOpRequest(api_op_request) => api_op_request.well_formed(),
            Message::APIOpResponse(api_op_response) => api_op_response.well_formed(),
            Message::APIWatchNotification(api_watch_notification) => api_watch_notification.well_formed(),
            Message::WorkloadSubmission(api_op_request) => api_op_request.well_formed(),
        }
    }
}

pub struct MessageOps {
    pub recv: Option<Message>,
    pub send: Option<Message>,
}

impl MessageOps {
    #[spec] #[verifier(publish)]
    pub fn recv_well_formed(&self) -> bool {
        match self.recv {
            Option::None => true,
            Option::Some(message) => message.well_formed(),
        }
    }

    #[spec] #[verifier(publish)]
    pub fn send_well_formed(&self) -> bool {
        match self.send {
            Option::None => true,
            Option::Some(message) => message.well_formed(),
        }
    }

    #[spec] #[verifier(publish)]
    pub fn well_formed(&self) -> bool {
        self.recv_well_formed()
        && self.send_well_formed()
    }
}

#[spec] #[verifier(publish)]
pub fn state_transition_by_api_op(cluster_state: ClusterState, cluster_state_prime: ClusterState, api_op: APIOp) -> bool {
    match api_op {
        APIOp::Get{object_key} => cluster_state.contains(object_key) && equal(cluster_state, cluster_state_prime),
        APIOp::Create{object_key, object} => !cluster_state.contains(object_key) && equal(cluster_state.state.insert(object_key, object), cluster_state_prime.state),
        APIOp::Update{object_key, object} => cluster_state.contains(object_key) && equal(cluster_state.state.insert(object_key, object), cluster_state_prime.state),
        APIOp::Delete{object_key} => cluster_state.contains(object_key) && equal(cluster_state.state.remove(object_key), cluster_state_prime.state),
        _ => false,
    }
}

}
