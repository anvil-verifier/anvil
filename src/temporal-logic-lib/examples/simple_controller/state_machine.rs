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

pub open spec fn init() -> StatePred<CState> {
    |s: CState| {
        &&& !s.sent_1_create
        &&& !s.sent_2_create
        &&& !s.obj_1_exists
        &&& !s.obj_2_exists
        &&& s.messages === Set::empty()
    }
}

pub open spec fn send1_pre() -> StatePred<CState> {
    |s: CState| {
        &&& !s.obj_1_exists
        &&& !s.sent_1_create
    }
}

pub open spec fn send1() -> ActionPred<CState> {
    |s, s_prime: CState| {
        &&& send1_pre()(s)
        &&& s_prime === CState {
            sent_1_create: true,
            messages: s.messages.insert(Message::CreateReq{id: 1}),
            ..s
        }
    }
}

pub open spec fn send2_pre() -> StatePred<CState> {
    |s: CState| {
        &&& s.obj_1_exists
        &&& !s.obj_2_exists
        &&& !s.sent_2_create
    }
}

pub open spec fn send2() -> ActionPred<CState> {
    |s, s_prime: CState| {
        &&& send2_pre()(s)
        &&& s_prime === CState {
            sent_2_create: true,
            messages: s.messages.insert(Message::CreateReq{id: 2}),
            ..s
        }
    }
}

pub open spec fn reconcile() -> ActionPred<CState> {
    |s, s_prime: CState| {
        ||| send1()(s, s_prime)
        ||| send2()(s, s_prime)
    }
}

pub open spec fn create1_pre() -> StatePred<CState> {
    |s: CState| s.messages.contains(Message::CreateReq{id: 1})
}

pub open spec fn create1() -> ActionPred<CState> {
    |s, s_prime: CState| {
        &&& create1_pre()(s)
        &&& s_prime === CState {
            obj_1_exists: true,
            ..s
        }
    }
}

pub open spec fn create2_pre() -> StatePred<CState> {
    |s: CState| s.messages.contains(Message::CreateReq{id: 2})
}

pub open spec fn create2() -> ActionPred<CState> {
    |s, s_prime: CState| {
        &&& create2_pre()(s)
        &&& s_prime === CState {
            obj_2_exists: true,
            ..s
        }
    }
}

pub open spec fn cluster() -> ActionPred<CState> {
    |s, s_prime: CState| {
        ||| create1()(s, s_prime)
        ||| create2()(s, s_prime)
    }
}

pub open spec fn stutter() -> ActionPred<CState> {
    |s, s_prime: CState| s === s_prime
}

pub open spec fn next() -> ActionPred<CState> {
    |s, s_prime: CState| {
        ||| reconcile()(s, s_prime)
        ||| cluster()(s, s_prime)
        ||| stutter()(s, s_prime)
    }
}

pub open spec fn sm_spec() -> TempPred<CState> {
    lift_state(init())
        .and(always(lift_action(next())))
        .and(weak_fairness(reconcile()))
        .and(weak_fairness(create1()))
        .and(weak_fairness(create2()))
}

pub proof fn send1_enabled()
    ensures
        forall |s: CState| state_pred_call(send1_pre(), s) ==> enabled(reconcile())(s),
{
    assert forall |s: CState| state_pred_call(send1_pre(), s) implies enabled(reconcile())(s) by {
        let witness_s_prime = CState {
            sent_1_create: true,
            messages: s.messages.insert(Message::CreateReq{id: 1}),
            ..s
        };
        assert(action_pred_call(reconcile(), s, witness_s_prime));
    };
}

pub proof fn send2_enabled()
    ensures
        forall |s: CState| state_pred_call(send2_pre(), s) ==> enabled(reconcile())(s),
{
    assert forall |s: CState| state_pred_call(send2_pre(), s) implies enabled(reconcile())(s) by {
        let witness_s_prime = CState {
            sent_2_create: true,
            messages: s.messages.insert(Message::CreateReq{id: 2}),
            ..s
        };
        assert(action_pred_call(reconcile(), s, witness_s_prime));
    };
}

pub proof fn create1_enabled()
    ensures
        forall |s: CState| state_pred_call(create1_pre(), s) ==> enabled(create1())(s),
{
    assert forall |s: CState| state_pred_call(create1_pre(), s) implies enabled(create1())(s) by {
        let witness_s_prime = CState {
            obj_1_exists: true,
            ..s
        };
        assert(action_pred_call(create1(), s, witness_s_prime));
    };
}

pub proof fn create2_enabled()
    ensures
        forall |s: CState| state_pred_call(create2_pre(), s) ==> enabled(create2())(s),
{
    assert forall |s: CState| state_pred_call(create2_pre(), s) implies enabled(create2())(s) by {
        let witness_s_prime = CState {
            obj_2_exists: true,
            ..s
        };
        assert(action_pred_call(create2(), s, witness_s_prime));
    };
}

}
