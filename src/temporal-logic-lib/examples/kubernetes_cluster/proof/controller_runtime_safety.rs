// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::kubernetes_cluster::{
    proof::kubernetes_api_safety,
    spec::{
        common::*,
        controller,
        controller::{relevant_cr_key, ControllerAction, ControllerActionInput, ReconcileCoreStep},
        distributed_system::*,
    },
};
use crate::pervasive::{option::*, result::*};
use crate::temporal_logic::*;
use crate::temporal_logic_rules::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn lemma_always_reconcile_init_implies_no_pending_req(cr_key: ResourceKey)
    ensures
        sm_spec().entails(always(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::Init
            })
                .implies(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::Init
                    &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
            }))
        )),
{
    init_invariant::<State>(sm_spec(),
        init(),
        next(),
        |s: State| {
            s.reconcile_state_contains(cr_key)
            && s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::Init
            ==> s.reconcile_state_contains(cr_key)
                && s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::Init
                && s.reconcile_state_of(cr_key).pending_req_msg.is_None()
        }
    );
    temp_pred_equality::<State>(
        lift_state(|s: State| {
            s.reconcile_state_contains(cr_key)
            && s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::Init
            ==> s.reconcile_state_contains(cr_key)
                && s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::Init
                && s.reconcile_state_of(cr_key).pending_req_msg.is_None()
        }),
        lift_state(|s: State| {
            &&& s.reconcile_state_contains(cr_key)
            &&& s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::Init
        }).implies(lift_state(|s: State| {
            &&& s.reconcile_state_contains(cr_key)
            &&& s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::Init
            &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
        }))
    );
}

}
