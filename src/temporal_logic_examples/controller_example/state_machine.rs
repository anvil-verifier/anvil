// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::set::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub enum Message {
    CreateReq{id: nat},
}

pub struct CState {
    pub sent_1_create: bool,
    pub sent_2_create: bool,
    pub obj_1_exists: bool,
    pub obj_2_exists: bool,
    pub messages: Set<Message>,
}

pub open spec fn init(s: CState) -> bool {
    &&& !s.sent_1_create
    &&& !s.sent_2_create
    &&& !s.obj_1_exists
    &&& !s.obj_2_exists
    &&& s.messages === Set::empty()
}

pub open spec fn send1_pre(s: CState) -> bool {
    &&& !s.obj_1_exists
    &&& !s.sent_1_create
}

pub open spec fn send1(s: CState, s_prime: CState) -> bool {
    &&& send1_pre(s)
    &&& s_prime === CState {
        sent_1_create: true,
        messages: s.messages.insert(Message::CreateReq{id: 1}),
        ..s
    }
}

pub open spec fn send2_pre(s: CState) -> bool {
    &&& s.obj_1_exists
    &&& !s.obj_2_exists
    &&& !s.sent_2_create
}

pub open spec fn send2(s: CState, s_prime: CState) -> bool {
    &&& send2_pre(s)
    &&& s_prime === CState {
        sent_2_create: true,
        messages: s.messages.insert(Message::CreateReq{id: 2}),
        ..s
    }
}

pub open spec fn reconcile(s: CState, s_prime: CState) -> bool {
    ||| send1(s, s_prime)
    ||| send2(s, s_prime)
}

pub open spec fn create1_pre(s: CState) -> bool {
    s.messages.contains(Message::CreateReq{id: 1})
}

pub open spec fn create1(s: CState, s_prime: CState) -> bool {
    &&& create1_pre(s)
    &&& s_prime === CState {
        obj_1_exists: true,
        ..s
    }
}

pub open spec fn create2_pre(s: CState) -> bool {
    s.messages.contains(Message::CreateReq{id: 2})
}

pub open spec fn create2(s: CState, s_prime: CState) -> bool {
    &&& create2_pre(s)
    &&& s_prime === CState {
        obj_2_exists: true,
        ..s
    }
}

pub open spec fn cluster(s: CState, s_prime: CState) -> bool {
    ||| create1(s, s_prime)
    ||| create2(s, s_prime)
}

pub open spec fn stutter(s: CState, s_prime: CState) -> bool {
    s === s_prime
}

pub open spec fn next(s: CState, s_prime: CState) -> bool {
    ||| reconcile(s, s_prime)
    ||| cluster(s, s_prime)
    ||| stutter(s, s_prime)
}

pub open spec fn send1_pre_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| send1_pre(state))
}

pub open spec fn send2_pre_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| send2_pre(state))
}

pub open spec fn create1_pre_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| create1_pre(state))
}

pub open spec fn create2_pre_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| create2_pre(state))
}

pub open spec fn reconcile_pre_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| send1_pre(state) || send2_pre(state))
}

pub open spec fn reconcile_action_pred() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| reconcile(action.state, action.state_prime))
}

pub open spec fn cluster_action_pred() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| cluster(action.state, action.state_prime))
}

pub open spec fn create1_action_pred() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| create1(action.state, action.state_prime))
}

pub open spec fn create2_action_pred() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| create2(action.state, action.state_prime))
}

pub open spec fn init_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| init(state))
}

pub open spec fn next_action_pred() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| next(action.state, action.state_prime))
}

pub open spec fn sm_spec() -> TempPred<CState> {
        init_state_pred().lift().and(
            always(next_action_pred().lift()).and(
                weak_fairness(reconcile_action_pred()).and(
                    weak_fairness(create1_action_pred()).and(
                        weak_fairness(create2_action_pred()))
            ),
        )
    )
}

}
