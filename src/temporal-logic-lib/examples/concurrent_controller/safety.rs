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
        sm_spec().entails(always(lift_state(|s: CState| {
            &&& s.vol_attached ==> resource_exists(s, new_strlit("app_sts_pod")@)
            &&& s.vol_attached ==> resource_exists(s, new_strlit("app_vol")@)
        }))),
{
    init_invariant::<CState>(sm_spec(),
        init(),
        next(),
        |s: CState| {
            &&& s.vol_attached ==> resource_exists(s, new_strlit("app_sts_pod")@)
            &&& s.vol_attached ==> resource_exists(s, new_strlit("app_vol")@)
        }
    );
}

}
