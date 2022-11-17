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

pub type KubernetesAPIAction = HostAction<State, Option<Message>, Set<Message>>;

pub type KubernetesAPIHostActionResult = HostActionResult<State, Set<Message>>;

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

pub open spec fn handle_request() -> KubernetesAPIAction {
    HostAction {
        precondition: |recv: Option<Message>, s| {
            &&& recv.is_Some()
            &&& recv.get_Some_0().is_CreateRequest() || recv.get_Some_0().is_DeleteRequest()
        },
        transition: |recv: Option<Message>, s| {
            (State {resources: update_resources_with(s, recv.get_Some_0())}, outcome_messages(s, recv.get_Some_0()))
        },
    }
}

pub enum Step {
    HandleRequest,
}

pub open spec fn valid_actions() -> Set<KubernetesAPIAction> {
    set![handle_request()]
}

pub proof fn exists_next_step(action: KubernetesAPIAction, recv: Option<Message>, s: State)
    requires
        valid_actions().contains(action),
        (action.precondition)(recv, s),
    ensures
        exists |step| (#[trigger] step_to_action(step).precondition)(recv, s),
{
    assert((step_to_action(Step::HandleRequest).precondition)(recv, s));
}

pub open spec fn step_to_action(step: Step) -> KubernetesAPIAction {
    match step {
        Step::HandleRequest => handle_request(),
    }
}

pub open spec fn next_result(recv: Option<Message>, s: State) -> KubernetesAPIHostActionResult {
    if exists |step| (#[trigger] step_to_action(step).precondition)(recv, s) {
        let witness_step = choose |step| (#[trigger] step_to_action(step).precondition)(recv, s);
        let action = step_to_action(witness_step);
        HostActionResult::Enabled((action.transition)(recv, s).0, (action.transition)(recv, s).1)
    } else {
        HostActionResult::Disabled
    }
}

}
