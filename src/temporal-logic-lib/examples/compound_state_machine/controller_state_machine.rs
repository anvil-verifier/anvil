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

pub struct ControllerState {}

pub open spec fn init(s: ControllerState) -> bool {
    true
}

pub open spec fn send_create_sts() -> HostAction<ControllerState, Option<Message>, Set<Message>> {
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

pub open spec fn send_delete_sts() -> HostAction<ControllerState, Option<Message>, Set<Message>> {
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

pub enum ControllerStep {
    SendCreateStsStep,
    SendDeleteStsStep,
}

pub open spec fn next_step(recv: Option<Message>, s: ControllerState, s_prime: ControllerState, step: ControllerStep) -> bool {
    match step {
        ControllerStep::SendCreateStsStep => send_create_sts().satisfied_by(recv, s, s_prime),
        ControllerStep::SendDeleteStsStep => send_delete_sts().satisfied_by(recv, s, s_prime),
    }
}

pub open spec fn next(recv: Option<Message>, s: ControllerState, s_prime: ControllerState) -> bool {
    exists |step| next_step(recv, s, s_prime, step)
}

pub open spec fn output(recv: Option<Message>, s: ControllerState, s_prime: ControllerState) -> Set<Message>
    recommends next(recv, s, s_prime)
{
    let witness_step = choose |step| next_step(recv, s, s_prime, step);
    match witness_step {
        ControllerStep::SendCreateStsStep => (send_create_sts().output)(recv, s),
        ControllerStep::SendDeleteStsStep => (send_delete_sts().output)(recv, s),
    }
}

}
