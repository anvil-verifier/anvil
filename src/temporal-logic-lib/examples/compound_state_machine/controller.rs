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

pub struct State {}

pub open spec fn init(s: State) -> bool {
    true
}

pub type ControllerAction = HostAction<State, Option<Message>, Set<Message>>;

pub type ControllerHostActionResult = HostActionResult<State, Set<Message>>;

pub open spec fn send_create_sts() -> ControllerAction {
    HostAction {
        precondition: |recv: Option<Message>, s| {
            &&& recv.is_Some()
            &&& recv.get_Some_0().is_CreateResponse()
            &&& recv.get_Some_0().get_CreateResponse_0().obj.key.kind.is_CustomResourceKind()
        },
        transition: |recv: Option<Message>, s| {
            s
        },
        output: |recv: Option<Message>, s| {
            set![create_req_msg(ResourceKey{
                name: recv.get_Some_0().get_CreateResponse_0().obj.key.name + sts_suffix(),
                kind: ResourceKind::StatefulSetKind
            })]
        }
    }
}

pub open spec fn send_delete_sts() -> ControllerAction {
    HostAction {
        precondition: |recv: Option<Message>, s| {
            &&& recv.is_Some()
            &&& recv.get_Some_0().is_DeleteResponse()
            &&& recv.get_Some_0().get_DeleteResponse_0().key.kind.is_CustomResourceKind()
        },
        transition: |recv: Option<Message>, s| {
            s
        },
        output: |recv: Option<Message>, s| {
            set![delete_req_msg(ResourceKey{
                name: recv.get_Some_0().get_DeleteResponse_0().key.name + sts_suffix(),
                kind: ResourceKind::StatefulSetKind
            })]
        }
    }
}

pub open spec fn valid_actions() -> Set<ControllerAction> {
    set![send_create_sts(), send_delete_sts()]
}

pub enum Step {
    SendCreateStsStep,
    SendDeleteStsStep,
}

pub proof fn exists_next_step(action: ControllerAction, recv: Option<Message>, s: State)
    requires
        valid_actions().contains(action),
        (action.precondition)(recv, s),
    ensures
        exists |step| (#[trigger] step_to_action(step).precondition)(recv, s),
{
    if action === send_create_sts() {
        assert((step_to_action(Step::SendCreateStsStep).precondition)(recv, s));
    } else {
        assert((step_to_action(Step::SendDeleteStsStep).precondition)(recv, s));
    }
}

pub open spec fn step_to_action(step: Step) -> ControllerAction {
    match step {
        Step::SendCreateStsStep => send_create_sts(),
        Step::SendDeleteStsStep => send_delete_sts(),
    }
}

pub open spec fn next_result(recv: Option<Message>, s: State) -> ControllerHostActionResult {
    if exists |step| (#[trigger] step_to_action(step).precondition)(recv, s) {
        let witness_step = choose |step| (#[trigger] step_to_action(step).precondition)(recv, s);
        let action = step_to_action(witness_step);
        HostActionResult::Enabled((action.transition)(recv, s), (action.output)(recv, s))
    } else {
        HostActionResult::Disabled
    }
}

}
