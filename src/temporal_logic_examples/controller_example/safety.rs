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

spec fn obj1_inv(s: CState) -> bool {
    &&& s.sent_2_create ==> s.obj_1_exists
    &&& s.obj_1_exists ==> s.sent_1_create
}

spec fn create_inv(s: CState) -> bool {
    s.obj_2_exists ==> s.sent_2_create && s.sent_1_create && s.obj_1_exists
}

pub open spec fn order_inv(s: CState) -> bool {
    s.obj_2_exists ==> s.obj_1_exists
}

spec fn inductive_inv(s: CState) -> bool {
    &&& msg_inv(s)
    &&& obj1_inv(s)
    &&& create_inv(s)
    &&& order_inv(s)
}

pub open spec fn msg_inv_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| msg_inv(state))
}

pub open spec fn order_inv_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| order_inv(state))
}

spec fn inductive_inv_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| inductive_inv(state))
}

proof fn lemma_inductive_inv()
    ensures
        valid(implies(sm_spec(), always(inductive_inv_state_pred().lift())))
{
    implies_apply_auto::<CState>();
    init_invariant::<CState>(init_state_pred(), next_action_pred(), inductive_inv_state_pred());
}

pub proof fn safety()
    ensures
        valid(implies(sm_spec(), always(order_inv_state_pred().lift())))
{
    implies_apply_auto::<CState>();
    lemma_inductive_inv();
    implies_generalize::<CState>(inductive_inv_state_pred().lift(), order_inv_state_pred().lift());
}

}
