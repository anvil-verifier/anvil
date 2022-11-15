// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::compound_state_machine::common::*;
use crate::pervasive::{map::*, option::*, seq::*, set::*, string::*};
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct State {
    pub resources: Map<ResourceKey, ResourceObj>,
}

pub open spec fn init(s: State) -> bool {
    s.resources === Map::empty()
}

pub open spec fn update_resources_with(s: State, msg: Message) -> Map<ResourceKey, ResourceObj>
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

pub open spec fn outcome_messages(s: State, msg: Message) -> Set<Message>
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

pub open spec fn handle_request_pre(s: State, msg: Message) -> bool {
    msg.is_CreateRequest() || msg.is_DeleteRequest()
}

pub open spec fn handle_request() -> HostAction<State, Option<Message>, Set<Message>> {
    HostAction {
        precondition: |recv: Option<Message>, s| {
            &&& recv.is_Some()
            &&& recv.get_Some_0().is_CreateRequest() || recv.get_Some_0().is_DeleteRequest()
        },
        transition: |recv: Option<Message>, s| {
            State {
                resources: update_resources_with(s, recv.get_Some_0()),
            }
        },
        output: |recv: Option<Message>, s| {
            outcome_messages(s, recv.get_Some_0())
        }
    }
}

pub enum KubernetesAPIStep {
    HandleRequest,
}

pub open spec fn valid_actions() -> Set<HostAction<State, Option<Message>, Set<Message>>> {
    set![handle_request()]
}

pub open spec fn next_step(recv: Option<Message>, s: State, s_prime: State, step: KubernetesAPIStep) -> bool {
    match step {
        KubernetesAPIStep::HandleRequest => handle_request().satisfied_by(recv, s, s_prime),
    }
}

pub open spec fn next(recv: Option<Message>, s: State, s_prime: State) -> bool {
    exists |step| next_step(recv, s, s_prime, step)
}

pub open spec fn output(recv: Option<Message>, s: State, s_prime: State) -> Set<Message>
    recommends next(recv, s, s_prime)
{
    let witness_step = choose |step| next_step(recv, s, s_prime, step);
    match witness_step {
        KubernetesAPIStep::HandleRequest => (handle_request().output)(recv, s),
    }
}

pub proof fn exists_step_for_valid_action(action: HostAction<State, Option<Message>, Set<Message>>, recv: Option<Message>, s: State, s_prime: State)
    requires
        valid_actions().contains(action),
        action.satisfied_by(recv, s, s_prime),
    ensures
        exists |step| next_step(recv, s, s_prime, step)
{
    assert(next_step(recv, s, s_prime, KubernetesAPIStep::HandleRequest));
}


}
