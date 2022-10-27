// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::concurrent_controller::state_machine::*;
use crate::pervasive::seq::*;
use crate::pervasive::string::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn lemma_always_attach_after_create(cr_name: Seq<char>)
    ensures
        sm_spec().entails(always(lift_state(|s: CState| {
            &&& s.attached.contains(cr_name) ==> message_sent(s, create_pod_resp_msg(cr_name + sts_suffix() + pod_suffix()))
            &&& s.attached.contains(cr_name) ==> message_sent(s, create_vol_resp_msg(cr_name + vol_suffix()))
        }))),
{
    init_invariant::<CState>(sm_spec(),
        init(),
        next(),
        |s: CState| {
            &&& s.attached.contains(cr_name) ==> message_sent(s, create_pod_resp_msg(cr_name + sts_suffix() + pod_suffix()))
            &&& s.attached.contains(cr_name) ==> message_sent(s, create_vol_resp_msg(cr_name + vol_suffix()))
        }
    );
}

}
