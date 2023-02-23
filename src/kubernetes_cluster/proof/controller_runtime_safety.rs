// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::{
    proof::{kubernetes_api_safety, wf1_assistant::controller_action_pre_implies_next_pre},
    spec::{
        common::*,
        controller::common::{ControllerAction, ControllerActionInput},
        controller::controller_runtime::{
            continue_reconcile, end_reconcile, run_scheduled_reconcile, trigger_reconcile,
        },
        controller::state_machine::controller,
        distributed_system::*,
        reconciler::Reconciler,
    },
};
use crate::pervasive::{option::*, result::*};
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn resp_matches_at_most_one_pending_req<T>(resp_msg: Message, cr_key: ResourceKey) -> StatePred<State<T>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<T>| {
        s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).pending_req_msg.is_Some()
        && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
        ==> (
            forall |other_key: ResourceKey|
                #[trigger] s.reconcile_state_contains(other_key)
                && s.reconcile_state_of(other_key).pending_req_msg.is_Some()
                && other_key !== cr_key
                ==> !resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(other_key).pending_req_msg.get_Some_0())
            )
    }
}

#[verifier(external_body)]
pub proof fn lemma_always_resp_matches_at_most_one_pending_req<T>(reconciler: Reconciler<T>, resp_msg: Message, cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(reconciler).entails(always(lift_state(resp_matches_at_most_one_pending_req(resp_msg, cr_key)))),
{}

}
