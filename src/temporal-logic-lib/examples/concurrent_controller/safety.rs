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
        sm_spec().entails(always(StatePred::new(|state| {
            &&& state.vol_attached ==> resource_exists(state, new_strlit("my_pod1")@)
            &&& state.vol_attached ==> resource_exists(state, new_strlit("my_volume1")@)
        }).lift())),
{
    init_invariant::<CState>(sm_spec(),
        StatePred::new(|state| init(state)),
        next(),
        StatePred::new(|state| {
            &&& state.vol_attached ==> resource_exists(state, new_strlit("my_pod1")@)
            &&& state.vol_attached ==> resource_exists(state, new_strlit("my_volume1")@)
        })
    );
}

}
