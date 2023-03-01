// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::{map::*, option::*, seq::*, set::*, string::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use crate::tla_examples::compound::common::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct State {}

pub enum Step {
    SendCreateStsStep,
    SendDeleteStsStep,
}

pub type ControllerStateMachine = StateMachine<State, Option<Message>, Option<Message>, Set<Message>, Step>;

pub type ControllerAction = Action<State, Option<Message>, Set<Message>>;

pub type ControllerActionResult = ActionResult<State, Set<Message>>;

pub open spec fn send_create_sts() -> ControllerAction {
    Action {
        precondition: |recv: Option<Message>, s| {
            &&& recv.is_Some()
            &&& recv.get_Some_0().is_CreateResponse()
            &&& recv.get_Some_0().get_CreateResponse_0().obj.key.kind.is_CustomResourceKind()
        },
        transition: |recv: Option<Message>, s| {
            (s, set![create_req_msg(ResourceKey{
                name: recv.get_Some_0().get_CreateResponse_0().obj.key.name + sts_suffix(),
                kind: ResourceKind::StatefulSetKind
            })])
        },
    }
}

pub open spec fn send_delete_sts() -> ControllerAction {
    Action {
        precondition: |recv: Option<Message>, s| {
            &&& recv.is_Some()
            &&& recv.get_Some_0().is_DeleteResponse()
            &&& recv.get_Some_0().get_DeleteResponse_0().key.kind.is_CustomResourceKind()
        },
        transition: |recv: Option<Message>, s| {
            (s, set![delete_req_msg(ResourceKey{
                name: recv.get_Some_0().get_DeleteResponse_0().key.name + sts_suffix(),
                kind: ResourceKind::StatefulSetKind
            })])
        },
    }
}

pub open spec fn controller() -> ControllerStateMachine {
    StateMachine {
        init: |s: State| true,
        actions: set![send_create_sts(), send_delete_sts()],
        step_to_action: |step: Step| {
            match step {
                Step::SendCreateStsStep => send_create_sts(),
                Step::SendDeleteStsStep => send_delete_sts(),
            }
        },
        action_input: |step: Step, recv: Option<Message>| {
            recv
        }
    }
}

pub proof fn exists_next_step(action: ControllerAction, recv: Option<Message>, s: State)
    requires
        controller().actions.contains(action),
        (action.precondition)(recv, s),
    ensures
        exists |step| (#[trigger] (controller().step_to_action)(step).precondition)(recv, s),
{
    if action == send_create_sts() {
        assert(((controller().step_to_action)(Step::SendCreateStsStep).precondition)(recv, s));
    } else {
        assert(((controller().step_to_action)(Step::SendDeleteStsStep).precondition)(recv, s));
    }
}

}
