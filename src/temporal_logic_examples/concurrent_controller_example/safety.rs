// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::concurrent_controller_example::state_machine::*;
use crate::pervasive::string::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn attach_after_create_inv(state: CState) -> bool {
    &&& state.vol_attached ==> state.resources.dom().contains(new_strlit("my_pod1")@)
    &&& state.vol_attached ==> state.resources.dom().contains(new_strlit("my_volume1")@)
}

pub open spec fn attach_after_create_inv_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| attach_after_create_inv(state))
}

pub proof fn lemma_attach_after_create_inv_state_pred()
    ensures
        valid(sm_spec().implies(always(attach_after_create_inv_state_pred().lift())))
{
    init_invariant::<CState>(sm_spec(), init_state_pred(), next_action_pred(), attach_after_create_inv_state_pred());
}

}
