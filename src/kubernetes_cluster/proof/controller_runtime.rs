// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::{common::*, resource::*};
use crate::kubernetes_cluster::{
    proof::{kubernetes_api_safety, wf1_assistant::controller_action_pre_implies_next_pre},
    spec::{
        cluster::*,
        controller::common::ControllerAction,
        controller::controller_runtime::{
            continue_reconcile, end_reconcile, run_scheduled_reconcile,
        },
        controller::state_machine::controller,
        message::*,
    },
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

pub open spec fn reconciler_init_and_no_pending_req
<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(cr_key: ObjectRef) -> StatePred<State<K, E, R>> {
    |s: State<K, E, R>| {
        &&& at_reconcile_state(cr_key, R::reconcile_init_state())(s)
        &&& no_pending_req_msg_or_external_api_input(s, cr_key)
    }
}

pub open spec fn reconciler_reconcile_init<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(cr_key: ObjectRef)
    -> StatePred<State<K, E, R>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<K, E, R>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& R::reconcile_init_state() == s.reconcile_state_of(cr_key).local_state
    }
}

pub open spec fn reconciler_reconcile_done<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(cr_key: ObjectRef)
    -> StatePred<State<K, E, R>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<K, E, R>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& R::reconcile_done(s.reconcile_state_of(cr_key).local_state)
    }
}

pub open spec fn reconciler_reconcile_error<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(cr_key: ObjectRef)
    -> StatePred<State<K, E, R>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<K, E, R>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& R::reconcile_error(s.reconcile_state_of(cr_key).local_state)
    }
}

pub open spec fn at_reconcile_state<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(key: ObjectRef, state: R::T) -> StatePred<State<K, E, R>>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: State<K, E, R>| {
        &&& s.reconcile_state_contains(key)
        &&& s.reconcile_state_of(key).local_state == state
    }
}

pub open spec fn at_expected_reconcile_states<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(key: ObjectRef, expected_states: FnSpec(R::T) -> bool) -> StatePred<State<K, E, R>>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: State<K, E, R>| {
        &&& s.reconcile_state_contains(key)
        &&& expected_states(s.reconcile_state_of(key).local_state)
    }
}

pub open spec fn pending_k8s_api_req_msg<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(s: State<K, E, R>, key: ObjectRef) -> bool {
    s.reconcile_state_of(key).pending_req_msg.is_Some()
    && s.reconcile_state_of(key).pending_external_api_input.is_None()
}

pub open spec fn pending_k8s_api_req_msg_is<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(s: State<K, E, R>, key: ObjectRef, req: Message) -> bool {
    s.reconcile_state_of(key).pending_req_msg == Option::Some(req)
    && s.reconcile_state_of(key).pending_external_api_input.is_None()
}

pub open spec fn no_pending_req_msg_or_external_api_input<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(s: State<K, E, R>, key: ObjectRef) -> bool {
    s.reconcile_state_of(key).pending_req_msg.is_None()
    && s.reconcile_state_of(key).pending_external_api_input.is_None()
}

pub open spec fn pending_req_in_flight_at_reconcile_state<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(key: ObjectRef, state: FnSpec(R::T) -> bool) -> StatePred<State<K, E, R>>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: State<K, E, R>| {
        at_expected_reconcile_states(key, state)(s)
        && pending_k8s_api_req_msg(s, key)
        && request_sent_by_controller(s.pending_req_of(key))
        && s.message_in_flight(s.pending_req_of(key))
    }
}

pub open spec fn request_sent_by_controller(msg: Message) -> bool {
    msg.src.is_CustomController()
    && msg.dst.is_KubernetesAPI()
    && msg.content.is_APIRequest()
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_reconcile_state<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    key: ObjectRef, state: FnSpec(R::T) -> bool, req_msg: Message
) -> StatePred<State<K, E, R>> {
    |s: State<K, E, R>| {
        at_expected_reconcile_states(key, state)(s)
        && pending_k8s_api_req_msg_is(s, key, req_msg)
        && request_sent_by_controller(req_msg)
        && s.message_in_flight(req_msg)
    }
}

pub open spec fn pending_req_in_flight_or_resp_in_flight_at_reconcile_state<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    key: ObjectRef, state: FnSpec(R::T) -> bool
) -> StatePred<State<K, E, R>>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: State<K, E, R>| {
        at_expected_reconcile_states(key, state)(s)
        ==> {
            pending_k8s_api_req_msg(s, key)
            && request_sent_by_controller(s.pending_req_of(key))
            && (s.message_in_flight(s.pending_req_of(key))
            || exists |resp_msg: Message| {
                #[trigger] s.message_in_flight(resp_msg)
                && resp_msg_matches_req_msg(resp_msg, s.pending_req_of(key))
            })
        }
    }
}

pub open spec fn pending_req_msg_is_none_at_reconcile_state<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    key: ObjectRef, state: FnSpec(R::T) -> bool
) -> StatePred<State<K, E, R>>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: State<K, E, R>| {
        at_expected_reconcile_states(key, state)(s)
        ==> s.reconcile_state_of(key).pending_req_msg.is_None()
    }
}

pub open spec fn no_pending_req_msg_or_external_api_input_at_reconcile_state<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    key: ObjectRef, state: FnSpec(R::T) -> bool
) -> StatePred<State<K, E, R>>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: State<K, E, R>| {
        at_expected_reconcile_states(key, state)(s)
        ==> no_pending_req_msg_or_external_api_input::<K, E, R>(s, key)
    }
}

pub open spec fn resp_in_flight_matches_pending_req_at_reconcile_state<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    key: ObjectRef, state: FnSpec(R::T) -> bool
) -> StatePred<State<K, E, R>>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: State<K, E, R>| {
        at_expected_reconcile_states(key, state)(s)
        && pending_k8s_api_req_msg(s, key)
        && request_sent_by_controller(s.pending_req_of(key))
        && exists |resp_msg: Message| {
            #[trigger] s.message_in_flight(resp_msg)
            && resp_msg_matches_req_msg(resp_msg, s.pending_req_of(key))
        }
    }
}

pub open spec fn no_pending_req_msg_or_external_api_input_at_reconcile_init_state<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    key: ObjectRef
) -> StatePred<State<K, E, R>>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: State<K, E, R>| {
        at_reconcile_state::<K, E, R>(key, R::reconcile_init_state())(s)
        ==> no_pending_req_msg_or_external_api_input(s, key)
    }
}

}
