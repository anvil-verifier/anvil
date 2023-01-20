// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::spec::{
    common::*,
    controller::common::{ControllerAction, ControllerActionInput},
    distributed_system::*,
};
use crate::pervasive::{option::*, result::*};
use crate::simple_controller::spec::{simple_reconciler, simple_reconciler::simple_reconciler};
use crate::temporal_logic::{defs::*, rules::*};
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn lemma_always_reconcile_init_implies_no_pending_req(cr_key: ResourceKey)
    ensures
        sm_spec(simple_reconciler()).entails(always(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
            })
                .implies(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
                    &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
            }))
        )),
{
    let invariant = |s: State| {
        s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
        ==> s.reconcile_state_contains(cr_key)
            && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
            && s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    };
    init_invariant::<State>(sm_spec(simple_reconciler()), init(simple_reconciler()), next(simple_reconciler()), invariant);

    // We intentionally write the safety property in a form that is friendly to liveness reasoning
    // There is no need to do this if we only want to prove safety
    let invariant_temp_pred = lift_state(|s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
    }).implies(lift_state(|s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    }));
    temp_pred_equality::<State>(lift_state(invariant), invariant_temp_pred);
}

pub proof fn lemma_always_reconcile_get_cr_done_implies_pending_get_cr_req(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(always(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
            })
                .implies(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
                    &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
                    &&& s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
                }))
        )),
{
    let invariant = |s: State| {
        s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
        ==> s.reconcile_state_contains(cr_key)
            && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
            && s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
            && s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
    };
    init_invariant::<State>(sm_spec(simple_reconciler()), init(simple_reconciler()), next(simple_reconciler()), invariant);

    let invariant_temp_pred = lift_state(|s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
    }).implies(lift_state(|s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
        &&& s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
    }));
    temp_pred_equality::<State>(lift_state(invariant), invariant_temp_pred);
}

pub proof fn lemma_always_reconcile_create_cm_done_implies_pending_create_cm_req(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(always(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
            })
                .implies(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
                    &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(simple_reconciler::create_cm_req(cr_key))))
                    &&& s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(simple_reconciler::create_cm_req(cr_key))))
                }))
        )),
{
    let invariant = |s: State| {
        s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
        ==> s.reconcile_state_contains(cr_key)
            && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
            && s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(simple_reconciler::create_cm_req(cr_key))))
            && s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(simple_reconciler::create_cm_req(cr_key))))
    };
    init_invariant::<State>(sm_spec(simple_reconciler()), init(simple_reconciler()), next(simple_reconciler()), invariant);

    let invariant_temp_pred = lift_state(|s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
    }).implies(lift_state(|s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(simple_reconciler::create_cm_req(cr_key))))
        &&& s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(simple_reconciler::create_cm_req(cr_key))))
    }));
    temp_pred_equality::<State>(lift_state(invariant), invariant_temp_pred);
}

}
