// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::compound_state_machine::common::*;
use crate::pervasive::{map::*, seq::*, set::*, string::*};
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct KubernetesAPIState {
    pub resources: Map<ResourceKey, ResourceObj>,
}

pub open spec fn init(s: KubernetesAPIState) -> bool {
    s.resources === Map::empty()
}

pub open spec fn update_resources_with(s: KubernetesAPIState, msg: Message) -> Map<ResourceKey, ResourceObj>
    recommends
        msg.is_CreateRequest() || msg.is_DeleteRequest(),
{
    if msg.is_CreateRequest() {
        if s.resources.dom().contains(msg.get_CreateRequest_0().obj.key) {
            s.resources
        } else {
            s.resources.insert(msg.get_CreateRequest_0().obj.key, msg.get_CreateRequest_0().obj)
        }
    } else {
        if !s.resources.dom().contains(msg.get_DeleteRequest_0().key) {
            s.resources
        } else {
            s.resources.remove(msg.get_DeleteRequest_0().key)
        }
    }
}

pub open spec fn outcome_messages(s: KubernetesAPIState, msg: Message) -> Set<Message>
    recommends
        msg.is_CreateRequest() || msg.is_DeleteRequest(),
{
    if msg.is_CreateRequest() {
        if msg.get_CreateRequest_0().obj.key.kind.is_StatefulSetKind() {
            set![
                create_resp_msg(msg.get_CreateRequest_0().obj.key),
                create_req_msg(ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + pod_suffix(), kind: ResourceKind::PodKind}),
                create_req_msg(ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + vol_suffix(), kind: ResourceKind::VolumeKind})
            ]
        } else {
            set![create_resp_msg(msg.get_CreateRequest_0().obj.key)]
        }
    } else {
        if msg.get_DeleteRequest_0().key.kind.is_StatefulSetKind() {
            set![
                delete_resp_msg(msg.get_DeleteRequest_0().key),
                delete_req_msg(ResourceKey{name: msg.get_DeleteRequest_0().key.name + pod_suffix(), kind: ResourceKind::PodKind}),
                delete_req_msg(ResourceKey{name: msg.get_DeleteRequest_0().key.name + vol_suffix(), kind: ResourceKind::VolumeKind})
            ]
        } else {
            set![delete_resp_msg(msg.get_DeleteRequest_0().key)]
        }
    }
}

pub open spec fn handle_request_pre(s: KubernetesAPIState, msg: Message) -> bool {
    msg.is_CreateRequest() || msg.is_DeleteRequest()
}

pub open spec fn handle_request(s: KubernetesAPIState, s_prime: KubernetesAPIState, msg_ops: MessageOps) -> bool {
    &&& msg_ops.recv.is_Some()
    &&& handle_request_pre(s, msg_ops.recv.get_Some_0())
    &&& s_prime === KubernetesAPIState {
        resources: update_resources_with(s, msg_ops.recv.get_Some_0()),
    }
    &&& msg_ops.send === outcome_messages(s, msg_ops.recv.get_Some_0())
}

pub enum KubernetesAPIStep {
    HandleRequest,
}

pub open spec fn next_step(s: KubernetesAPIState, s_prime: KubernetesAPIState, msg_ops: MessageOps, step: KubernetesAPIStep) -> bool {
    match step {
        KubernetesAPIStep::HandleRequest => handle_request(s, s_prime, msg_ops),
    }
}

pub open spec fn next(s: KubernetesAPIState, s_prime: KubernetesAPIState, msg_ops: MessageOps) -> bool {
    exists |step| next_step(s, s_prime, msg_ops, step)
}

}
