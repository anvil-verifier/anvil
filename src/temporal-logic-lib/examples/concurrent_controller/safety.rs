// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::concurrent_controller::state_machine::*;
use crate::pervasive::string::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn lemma_always_attach_after_create()
    ensures
        sm_spec().entails(always(lift_state(|state: CState| {
            &&& state.vol_attached ==> resource_exists(state, new_strlit("my_pod1")@)
            &&& state.vol_attached ==> resource_exists(state, new_strlit("my_volume1")@)
        }))),
{
    init_invariant::<CState>(sm_spec(),
        init(),
        next(),
        |state: CState| {
            &&& state.vol_attached ==> resource_exists(state, new_strlit("my_pod1")@)
            &&& state.vol_attached ==> resource_exists(state, new_strlit("my_volume1")@)
        }
    );
}

}
