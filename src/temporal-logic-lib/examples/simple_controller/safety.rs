// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::simple_controller::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn msg_inv() -> StatePred<CState> {
    |s: CState| {
        &&& s.sent_1_create <==> s.messages.contains(Message::CreateReq{id: 1})
        &&& s.sent_2_create <==> s.messages.contains(Message::CreateReq{id: 2})
    }
}

spec fn obj1_inv() -> StatePred<CState> {
    |s: CState| {
        &&& s.sent_2_create ==> s.obj_1_exists
        &&& s.obj_1_exists ==> s.sent_1_create
    }
}

pub open spec fn order_inv() -> StatePred<CState> {
    |s: CState| s.obj_2_exists ==> s.obj_1_exists
}

spec fn inductive_inv() -> StatePred<CState> {
    |s: CState| {
        &&& msg_inv()(s)
        &&& obj1_inv()(s)
        &&& order_inv()(s)
    }
}

proof fn lemma_inductive_inv()
    ensures
        sm_spec().entails(
            always(lift_state(inductive_inv()))
        ),
{
    init_invariant::<CState>(sm_spec(), init(), next(), inductive_inv());
}

pub proof fn safety()
    ensures
        sm_spec().entails(
            always(lift_state(order_inv()))
        ),
{
    lemma_inductive_inv();
    always_weaken::<CState>(sm_spec(), inductive_inv(), order_inv());
}

}
