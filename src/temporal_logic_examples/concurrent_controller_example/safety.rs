// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::concurrent_controller_example::state_machine::*;
use crate::pervasive::string::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn attach_after_create() -> StatePred<CState> {
    StatePred::new(|state: CState| {
        &&& state.vol_attached ==> state.resources.dom().contains(new_strlit("my_pod1")@)
        &&& state.vol_attached ==> state.resources.dom().contains(new_strlit("my_volume1")@)
    })
}

pub proof fn lemma_always_attach_after_create()
    ensures
        valid(sm_spec().implies(always(attach_after_create().lift())))
{
    init_invariant::<CState>(sm_spec(), init(), next(), attach_after_create());
}

}
