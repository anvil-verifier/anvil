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

pub open spec fn next_step(recv: Option<Message>, s: State, s_prime: State, step: Step) -> bool {
    match step {
        Step::SendCreateStsStep => send_create_sts().satisfied_by(recv, s, s_prime),
        Step::SendDeleteStsStep => send_delete_sts().satisfied_by(recv, s, s_prime),
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
        Step::SendCreateStsStep => (send_create_sts().output)(recv, s),
        Step::SendDeleteStsStep => (send_delete_sts().output)(recv, s),
    }
}

pub proof fn exists_next_step(action: ControllerAction, recv: Option<Message>, s: State, s_prime: State)
    requires
        valid_actions().contains(action),
        action.satisfied_by(recv, s, s_prime),
    ensures
        next(recv, s, s_prime)
{
    if action === send_create_sts() {
        assert(next_step(recv, s, s_prime, Step::SendCreateStsStep));
    } else {
        assert(next_step(recv, s, s_prime, Step::SendDeleteStsStep));
    }
}

}
