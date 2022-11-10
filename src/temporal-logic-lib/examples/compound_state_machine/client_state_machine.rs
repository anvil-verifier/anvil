// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::compound_state_machine::common::*;
use crate::pervasive::{seq::*, set::*};
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct ClientState {}

pub open spec fn init(s: ClientState) -> bool {
    true
}

pub open spec fn send_create_cr(s: ClientState, s_prime: ClientState, msg_ops: MessageOps, res: ResourceObj) -> bool {
    &&& res.key.kind.is_CustomResourceKind()
    &&& msg_ops.recv.is_None()
    &&& msg_ops.send === Set::empty().insert(create_req_msg(res.key))
}

pub open spec fn send_delete_cr(s: ClientState, s_prime: ClientState, msg_ops: MessageOps, res: ResourceObj) -> bool {
    &&& res.key.kind.is_CustomResourceKind()
    &&& msg_ops.recv.is_None()
    &&& msg_ops.send === Set::empty().insert(delete_req_msg(res.key))
}

pub enum ClientStep {
    SendCreateCrStep(ResourceObj),
    SendDeleteCrStep(ResourceObj),
}

pub open spec fn next_step(s: ClientState, s_prime: ClientState, msg_ops: MessageOps, step: ClientStep) -> bool {
    match step {
        ClientStep::SendCreateCrStep(res) => send_create_cr(s, s_prime, msg_ops, res),
        ClientStep::SendDeleteCrStep(res) => send_delete_cr(s, s_prime, msg_ops, res),
    }
}

pub open spec fn next(s: ClientState, s_prime: ClientState, msg_ops: MessageOps) -> bool {
    exists |step| next_step(s, s_prime, msg_ops, step)
}

}
