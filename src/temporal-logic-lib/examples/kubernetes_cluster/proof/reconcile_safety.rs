// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::kubernetes_cluster::{
    proof::kubernetes_api_safety,
    spec::{
        common::*,
        controller::common::{ControllerAction, ControllerActionInput, ReconcileCoreStep},
        controller::simple_controller,
        distributed_system::*,
    },
};
use crate::pervasive::{option::*, result::*};
use crate::temporal_logic::*;
use crate::temporal_logic_rules::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn lemma_always_reconcile_get_cr_done_implies_pending_get_cr_req(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(always(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::GetCRDone
            })
                .implies(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::GetCRDone
                    &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
                    &&& s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
                }))
        )),
{
    let invariant = |s: State| {
        s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::GetCRDone
        ==> s.reconcile_state_contains(cr_key)
            && s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::GetCRDone
            && s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
            && s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
    };
    init_invariant::<State>(sm_spec(), init(), next(), invariant);

    // We intentionally write the safety property in a form that is friendly to liveness reasoning
    // There is no need to do this if we only want to prove safety
    let invariant_temp_pred = lift_state(|s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::GetCRDone
    }).implies(lift_state(|s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::GetCRDone
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
        &&& s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
    }));
    temp_pred_equality::<State>(lift_state(invariant), invariant_temp_pred);
}

pub proof fn lemma_always_reconcile_create_cm_done_implies_pending_create_cm_req(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(always(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::CreateCMDone
            })
                .implies(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::CreateCMDone
                    &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(simple_controller::create_cm_req(cr_key))))
                    &&& s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(simple_controller::create_cm_req(cr_key))))
                }))
        )),
{
    let invariant = |s: State| {
        s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::CreateCMDone
        ==> s.reconcile_state_contains(cr_key)
            && s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::CreateCMDone
            && s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(simple_controller::create_cm_req(cr_key))))
            && s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(simple_controller::create_cm_req(cr_key))))
    };
    init_invariant::<State>(sm_spec(), init(), next(), invariant);

    let invariant_temp_pred = lift_state(|s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::CreateCMDone
    }).implies(lift_state(|s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::CreateCMDone
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(simple_controller::create_cm_req(cr_key))))
        &&& s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(simple_controller::create_cm_req(cr_key))))
    }));
    temp_pred_equality::<State>(lift_state(invariant), invariant_temp_pred);
}

}
