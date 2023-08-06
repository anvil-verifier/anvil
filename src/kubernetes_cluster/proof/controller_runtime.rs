// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::{common::*, resource::*};
use crate::kubernetes_cluster::spec::{
    cluster::*, controller::common::ControllerAction, controller::state_machine::*, message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn reconciler_init_and_no_pending_req(cr_key: ObjectRef) -> StatePred<Self> {
    |s: Self| {
        &&& Self::at_reconcile_state(cr_key, R::reconcile_init_state())(s)
        &&& Self::no_pending_req_msg_or_external_api_input(s, cr_key)
    }
}

pub open spec fn reconciler_reconcile_init(cr_key: ObjectRef)
    -> StatePred<Self>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        &&& s.reconcile_state_contains(cr_key)
        &&& R::reconcile_init_state() == s.reconcile_state_of(cr_key).local_state
    }
}

pub open spec fn reconciler_reconcile_done(cr_key: ObjectRef)
    -> StatePred<Self>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        &&& s.reconcile_state_contains(cr_key)
        &&& R::reconcile_done(s.reconcile_state_of(cr_key).local_state)
    }
}

pub open spec fn reconciler_reconcile_error(cr_key: ObjectRef)
    -> StatePred<Self>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        &&& s.reconcile_state_contains(cr_key)
        &&& R::reconcile_error(s.reconcile_state_of(cr_key).local_state)
    }
}

pub open spec fn at_reconcile_state(key: ObjectRef, state: R::T) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: Self| {
        &&& s.reconcile_state_contains(key)
        &&& s.reconcile_state_of(key).local_state == state
    }
}

pub open spec fn at_expected_reconcile_states(key: ObjectRef, expected_states: FnSpec(R::T) -> bool) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: Self| {
        &&& s.reconcile_state_contains(key)
        &&& expected_states(s.reconcile_state_of(key).local_state)
    }
}

pub open spec fn pending_k8s_api_req_msg(s: Self, key: ObjectRef) -> bool {
    s.reconcile_state_of(key).pending_req_msg.is_Some()
    && s.reconcile_state_of(key).pending_external_api_input.is_None()
}

pub open spec fn pending_k8s_api_req_msg_is(s: Self, key: ObjectRef, req: Message) -> bool {
    s.reconcile_state_of(key).pending_req_msg == Option::Some(req)
    && s.reconcile_state_of(key).pending_external_api_input.is_None()
}

pub open spec fn no_pending_req_msg_or_external_api_input(s: Self, key: ObjectRef) -> bool {
    s.reconcile_state_of(key).pending_req_msg.is_None()
    && s.reconcile_state_of(key).pending_external_api_input.is_None()
}

pub open spec fn pending_req_in_flight_at_reconcile_state(key: ObjectRef, state: FnSpec(R::T) -> bool) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        Self::at_expected_reconcile_states(key, state)(s)
        && Self::pending_k8s_api_req_msg(s, key)
        && Self::request_sent_by_controller(s.pending_req_of(key))
        && s.message_in_flight(s.pending_req_of(key))
    }
}

pub open spec fn request_sent_by_controller(msg: Message) -> bool {
    msg.src.is_CustomController()
    && msg.dst.is_KubernetesAPI()
    && msg.content.is_APIRequest()
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_reconcile_state(
    key: ObjectRef, state: FnSpec(R::T) -> bool, req_msg: Message
) -> StatePred<Self> {
    |s: Self| {
        Self::at_expected_reconcile_states(key, state)(s)
        && Self::pending_k8s_api_req_msg_is(s, key, req_msg)
        && Self::request_sent_by_controller(req_msg)
        && s.message_in_flight(req_msg)
    }
}

pub open spec fn pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
    key: ObjectRef, state: FnSpec(R::T) -> bool
) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        Self::at_expected_reconcile_states(key, state)(s)
        ==> {
            Self::pending_k8s_api_req_msg(s, key)
            && Self::request_sent_by_controller(s.pending_req_of(key))
            && (s.message_in_flight(s.pending_req_of(key))
            || exists |resp_msg: Message| {
                #[trigger] s.message_in_flight(resp_msg)
                && resp_msg_matches_req_msg(resp_msg, s.pending_req_of(key))
            })
        }
    }
}

pub open spec fn pending_req_msg_is_none_at_reconcile_state(
    key: ObjectRef, state: FnSpec(R::T) -> bool
) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        Self::at_expected_reconcile_states(key, state)(s)
        ==> s.reconcile_state_of(key).pending_req_msg.is_None()
    }
}

pub open spec fn no_pending_req_msg_or_external_api_input_at_reconcile_state(
    key: ObjectRef, state: FnSpec(R::T) -> bool
) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        Self::at_expected_reconcile_states(key, state)(s)
        ==> Self::no_pending_req_msg_or_external_api_input(s, key)
    }
}

pub open spec fn resp_in_flight_matches_pending_req_at_reconcile_state(
    key: ObjectRef, state: FnSpec(R::T) -> bool
) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        Self::at_expected_reconcile_states(key, state)(s)
        && Self::pending_k8s_api_req_msg(s, key)
        && Self::request_sent_by_controller(s.pending_req_of(key))
        && exists |resp_msg: Message| {
            #[trigger] s.message_in_flight(resp_msg)
            && resp_msg_matches_req_msg(resp_msg, s.pending_req_of(key))
        }
    }
}

pub open spec fn no_pending_req_msg_or_external_api_input_at_reconcile_init_state(
    key: ObjectRef
) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: Self| {
        Self::at_reconcile_state(key, R::reconcile_init_state())(s)
        ==> Self::no_pending_req_msg_or_external_api_input(s, key)
    }
}

}

}
