// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::compound_state_machine::common::*;
use crate::pervasive::{map::*, seq::*, set::*, string::*};
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct ControllerState {}

pub open spec fn init(s: ControllerState) -> bool {
    true
}

pub open spec fn send_create_sts_pre(s: ControllerState, msg: Message) -> bool {
    &&& msg.is_CreateResponse()
    &&& msg.get_CreateResponse_0().obj.key.kind.is_CustomResourceKind()
}

pub open spec fn send_create_sts(s: ControllerState, s_prime: ControllerState, msg_ops: MessageOps) -> bool {
    &&& msg_ops.recv.is_Some()
    &&& send_create_sts_pre(s, msg_ops.recv.get_Some_0())
    &&& s_prime === s
    &&& msg_ops.send === Set::empty().insert(create_req_msg(ResourceKey{
            name: msg_ops.recv.get_Some_0().get_CreateResponse_0().obj.key.name + sts_suffix(),
            kind: ResourceKind::StatefulSetKind
        }))
}

pub open spec fn send_delete_sts_pre(s: ControllerState, msg: Message) -> bool {
    &&& msg.is_DeleteResponse()
    &&& msg.get_DeleteResponse_0().key.kind.is_CustomResourceKind()
}

pub open spec fn send_delete_sts(s: ControllerState, s_prime: ControllerState, msg_ops: MessageOps) -> bool {
    &&& msg_ops.recv.is_Some()
    &&& send_delete_sts_pre(s, msg_ops.recv.get_Some_0())
    &&& s_prime === s
    &&& msg_ops.send === Set::empty().insert(delete_req_msg(ResourceKey{
            name: msg_ops.recv.get_Some_0().get_DeleteResponse_0().key.name + sts_suffix(),
            kind: ResourceKind::StatefulSetKind
        }))
}

pub enum ControllerStep {
    SendCreateStsStep,
    SendDeleteStsStep,
}

pub open spec fn next_step(s: ControllerState, s_prime: ControllerState, msg_ops: MessageOps, step: ControllerStep) -> bool {
    match step {
        ControllerStep::SendCreateStsStep => send_create_sts(s, s_prime, msg_ops),
        ControllerStep::SendDeleteStsStep => send_delete_sts(s, s_prime, msg_ops),
    }
}

pub open spec fn next(s: ControllerState, s_prime: ControllerState, msg_ops: MessageOps) -> bool {
    exists |step| next_step(s, s_prime, msg_ops, step)
}

}
