// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::controller_example::state_machine::*;
use crate::pred::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn msg_inv(s: CState) -> bool {
    &&& s.sent_1_create <==> s.messages.contains(Message::CreateReq{id: 1})
    &&& s.sent_2_create <==> s.messages.contains(Message::CreateReq{id: 2})
}

pub open spec fn obj1_inv(s: CState) -> bool {
    &&& s.sent_2_create ==> s.obj_1_exists
    &&& s.obj_1_exists ==> s.sent_1_create
}

pub open spec fn create_inv(s: CState) -> bool {
    s.obj_2_exists ==> s.sent_2_create && s.sent_1_create && s.obj_1_exists
}

pub open spec fn safety(s: CState) -> bool {
    s.obj_2_exists ==> s.obj_1_exists
}

pub open spec fn inductive_inv(s: CState) -> bool {
    &&& msg_inv(s)
    &&& obj1_inv(s)
    &&& create_inv(s)
    &&& safety(s)
}

pub open spec fn msg_inv_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| msg_inv(state))
}

// pub open spec fn obj1_inv_state_pred() -> StatePred<CState> {
//     StatePred::new(|state: CState| obj1_inv(state))
// }

// pub open spec fn create_inv_state_pred() -> StatePred<CState> {
//     StatePred::new(|state: CState| create_inv(state))
// }

pub open spec fn safety_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| safety(state))
}

pub open spec fn inductive_inv_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| inductive_inv(state))
}

pub proof fn prove_msg_inv()
    ensures
        valid(implies(sm_spec(), always(msg_inv_state_pred().lift())))
{
    apply_implies_auto::<CState>();
    init_invariant::<CState>(init_state_pred(), next_action_pred(), msg_inv_state_pred());
}

pub proof fn prove_inductive_inv()
    ensures
        valid(implies(sm_spec(), always(inductive_inv_state_pred().lift())))
{
    apply_implies_auto::<CState>();
    init_invariant::<CState>(init_state_pred(), next_action_pred(), inductive_inv_state_pred());
}

pub proof fn prove_safety()
    ensures
        valid(implies(sm_spec(), always(safety_state_pred().lift())))
{
    apply_implies_auto::<CState>();
    prove_inductive_inv();
    implies_generalize::<CState>(inductive_inv_state_pred().lift(), safety_state_pred().lift());
}

}
