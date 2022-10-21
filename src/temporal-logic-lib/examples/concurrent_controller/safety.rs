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
        valid(sm_spec().implies(always(StatePred::new(|state: CState| {
            &&& state.vol_attached ==> state.resources.dom().contains(new_strlit("my_pod1")@)
            &&& state.vol_attached ==> state.resources.dom().contains(new_strlit("my_volume1")@)
        }).lift()))),
{
    init_invariant::<CState>(sm_spec(),
        StatePred::new(|state: CState| init(state)),
        next(),
        StatePred::new(|state: CState| {
            &&& state.vol_attached ==> state.resources.dom().contains(new_strlit("my_pod1")@)
            &&& state.vol_attached ==> state.resources.dom().contains(new_strlit("my_volume1")@)
        })
    );
}

}
