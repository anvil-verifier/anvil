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
#[is_variant]
pub enum ReconcileStep {
    Init,
    CustomReconcileStep(CustomReconcileStep), // The argument is defined by the controller developer
    Retry,
    Done,
}

// TODO: we should strictly follow the object layout in
// https://github.com/kubernetes/kubernetes/blob/release-1.25/staging/src/k8s.io/apimachinery/pkg/apis/meta/v1/types.go

#[derive(PartialEq, Eq)]
pub struct ObjectMetaL {
    pub name: StringL,
    pub namespace: StringL,
    // TODO: use OwnerReferences instead of owner_key
    pub owner_key: ObjectKey,
}

#[derive(PartialEq, Eq)]
pub struct PodL {
    pub metadata: ObjectMetaL,
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
    pub metadata: ObjectMetaL,
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
#[is_variant]
pub enum KubernetesObject {
    Pod(PodL),
    ConfigMap(ConfigMapL),
    CustomResourceObject(CustomResourceObject),
}

impl KubernetesObject {
    pub open spec fn key(&self) -> ObjectKey {
        match *self {
            KubernetesObject::Pod(p) => p.key(),
            KubernetesObject::ConfigMap(cm) => cm.key(),
            KubernetesObject::CustomResourceObject(cro) => cro.key(),
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
        self.state === Map::empty()
    }

    pub open spec fn get(&self, object_key:ObjectKey) -> Option<KubernetesObject> {
        if self.state.dom().contains(object_key) {
            Option::Some(self.state.index(object_key))
        } else {
            Option::None
        }
    }

    pub open spec fn contains(&self, object_key:ObjectKey) -> bool {
        self.state.dom().contains(object_key)
    }

    pub open spec fn len(&self) -> nat {
        self.state.dom().len()
    }

    pub open spec fn well_formed(&self) -> bool {
        forall |key:ObjectKey| #[trigger] self.state.dom().contains(key) ==> self.state.index(key).key() === key
    }
}

#[derive(PartialEq, Eq)]
#[is_variant]
pub enum APIOp {
    Get{object_key: ObjectKey},
    Create{object_key: ObjectKey, object:KubernetesObject},
    Update{object_key: ObjectKey, object:KubernetesObject},
    Delete{object_key: ObjectKey},
}

impl APIOp {
    pub open spec fn well_formed(&self) -> bool {
        match *self {
            APIOp::Create{object_key, object} => object.key() === object_key,
            APIOp::Update{object_key, object} => object.key() === object_key,
            _ => true,
        }
    }

    pub open spec fn key(&self) -> ObjectKey {
        match *self {
            APIOp::Get{object_key} => object_key,
            APIOp::Create{object_key, ..} => object_key,
            APIOp::Update{object_key, ..} => object_key,
            APIOp::Delete{object_key} => object_key,
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
        self.api_op.key()
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
                APIOp::Get{object_key} => self.optional_object.get_Some_0().key() === object_key,
                APIOp::Create{object_key, ..} => self.optional_object.get_Some_0().key() === object_key,
                APIOp::Update{object_key, ..} => self.optional_object.get_Some_0().key() === object_key,
                APIOp::Delete{object_key} => self.optional_object.get_Some_0().key() === object_key,
            }
        )
    }

    pub open spec fn key(&self) -> ObjectKey {
        self.api_op_request.api_op.key()
    }
}

#[is_variant]
pub enum APIEvent {
    Added{object_key: ObjectKey, object:KubernetesObject},
    Modified{object_key: ObjectKey, object:KubernetesObject},
    Deleted{object_key: ObjectKey, object:KubernetesObject},
}

pub struct APIEventNotification {
    pub api_event: APIEvent,
}

impl APIEventNotification {
    pub open spec fn well_formed(&self) -> bool {
        true
    }

    pub open spec fn key(&self) -> ObjectKey {
        match self.api_event {
            APIEvent::Added{object_key, ..} => object_key,
            APIEvent::Modified{object_key, ..} => object_key,
            APIEvent::Deleted{object_key, ..} => object_key,
        }
    }

    pub open spec fn object(&self) -> KubernetesObject {
        match self.api_event {
            APIEvent::Added{object_key, object} => object,
            APIEvent::Modified{object_key, object} => object,
            APIEvent::Deleted{object_key, object} => object,
        }
    }
}

#[is_variant]
pub enum Payload {
    APIOpRequest(APIOpRequest),
    APIOpResponse(APIOpResponse),
    APIEventNotification(APIEventNotification),
}

impl Payload {
    pub open spec fn well_formed(&self) -> bool {
        match *self {
            Payload::APIOpRequest(api_op_request) => api_op_request.well_formed(),
            Payload::APIOpResponse(api_op_response) => api_op_response.well_formed(),
            Payload::APIEventNotification(api_event_notification) => api_event_notification.well_formed(),
        }
    }
}

#[is_variant]
pub enum HostId {
    KubernetesAPI,
    CustomController,
    CustomClient,
}

pub struct Message {
    pub src: HostId,
    pub dst: HostId,
    pub payload: Payload,
}

impl Message {
    pub open spec fn well_formed(&self) -> bool {
        self.payload.well_formed()
        && self.src !== self.dst
    }
}

pub struct NetworkOps {
    pub recv: Option<Message>,
    pub send: Option<Message>,
}

impl NetworkOps {
    pub open spec fn recv_well_formed(&self) -> bool {
        match self.recv {
            Option::None => true,
            Option::Some(message) => message.well_formed(),
        }
    }

    pub open spec fn send_well_formed(&self) -> bool {
        match self.send {
            Option::None => true,
            Option::Some(message) => message.well_formed(),
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
