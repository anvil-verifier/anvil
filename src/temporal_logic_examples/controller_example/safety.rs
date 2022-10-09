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
    &&& s.sent_1_create ==> s.messages.contains(Message::CreateReq{id: 1})
    &&& s.sent_2_create ==> s.messages.contains(Message::CreateReq{id: 2})
    &&& s.messages.contains(Message::CreateReq{id: 1}) ==> s.sent_1_create
    &&& s.messages.contains(Message::CreateReq{id: 2}) ==> s.sent_2_create
}

pub open spec fn msg_inv_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| msg_inv(state))
}

pub open spec fn msg_inv_always_holds() -> TempPred<CState> {
    implies(
        sm_spec(),
        always(msg_inv_state_pred().lift())
    )
}

pub proof fn prove_msg_inv()
    ensures
        valid(msg_inv_always_holds())
{
    apply_implies_auto::<CState>();
    init_invariant::<CState>(init_state_pred(), next_action_pred(), msg_inv_state_pred());
}

}
