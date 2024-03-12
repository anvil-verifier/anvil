// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::spec::{common::*, resource::*};
use crate::kubernetes_cluster::spec::{
    cluster::*, controller::state_machine::*, controller::types::ControllerAction, message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

impl <K: CustomResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn reconciler_init_and_no_pending_req(cr_key: ObjectRef) -> StatePred<Self> {
    |s: Self| {
        &&& Self::at_reconcile_state(cr_key, R::reconcile_init_state())(s)
        &&& Self::no_pending_req_msg(s, cr_key)
    }
}

pub open spec fn reconciler_reconcile_init(cr_key: ObjectRef)
    -> StatePred<Self>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        &&& s.ongoing_reconciles().contains_key(cr_key)
        &&& R::reconcile_init_state() == s.ongoing_reconciles()[cr_key].local_state
    }
}

pub open spec fn reconciler_reconcile_done(cr_key: ObjectRef)
    -> StatePred<Self>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        &&& s.ongoing_reconciles().contains_key(cr_key)
        &&& R::reconcile_done(s.ongoing_reconciles()[cr_key].local_state)
    }
}

pub open spec fn reconciler_reconcile_error(cr_key: ObjectRef)
    -> StatePred<Self>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        &&& s.ongoing_reconciles().contains_key(cr_key)
        &&& R::reconcile_error(s.ongoing_reconciles()[cr_key].local_state)
    }
}

pub open spec fn at_reconcile_state(key: ObjectRef, state: R::T) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: Self| {
        &&& s.ongoing_reconciles().contains_key(key)
        &&& s.ongoing_reconciles()[key].local_state == state
    }
}

pub open spec fn at_expected_reconcile_states(key: ObjectRef, expected_states: spec_fn(R::T) -> bool) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: Self| {
        &&& s.ongoing_reconciles().contains_key(key)
        &&& expected_states(s.ongoing_reconciles()[key].local_state)
    }
}

pub open spec fn has_pending_k8s_api_req_msg(s: Self, key: ObjectRef) -> bool {
    s.ongoing_reconciles()[key].pending_req_msg.is_Some()
    && s.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.is_APIRequest()
}

pub open spec fn has_pending_req_msg(s: Self, key: ObjectRef) -> bool {
    s.ongoing_reconciles()[key].pending_req_msg.is_Some()
    && (s.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.is_APIRequest()
        || s.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.is_ExternalAPIRequest())
}

pub open spec fn pending_req_msg_is(s: Self, key: ObjectRef, req: MsgType<E>) -> bool {
    s.ongoing_reconciles()[key].pending_req_msg == Some(req)
}

pub open spec fn no_pending_req_msg(s: Self, key: ObjectRef) -> bool {
    s.ongoing_reconciles()[key].pending_req_msg.is_None()
}

pub open spec fn pending_req_in_flight_at_reconcile_state(key: ObjectRef, state: spec_fn(R::T) -> bool) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        Self::at_expected_reconcile_states(key, state)(s)
        && Self::has_pending_req_msg(s, key)
        && Self::request_sent_by_controller(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
        && s.in_flight().contains(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
    }
}

pub open spec fn request_sent_by_controller(msg: MsgType<E>) -> bool {
    &&& msg.src.is_CustomController()
    &&& {
        ||| {
            &&& msg.dst.is_ApiServer()
            &&& msg.content.is_APIRequest()
        }
        ||| {
            &&& msg.dst.is_ExternalAPI()
            &&& msg.content.is_ExternalAPIRequest()
        }
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_reconcile_state(
    key: ObjectRef, state: spec_fn(R::T) -> bool, req_msg: MsgType<E>
) -> StatePred<Self> {
    |s: Self| {
        Self::at_expected_reconcile_states(key, state)(s)
        && Self::pending_req_msg_is(s, key, req_msg)
        && Self::request_sent_by_controller(req_msg)
        && s.in_flight().contains(req_msg)
    }
}

pub open spec fn pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
    key: ObjectRef, state: spec_fn(R::T) -> bool
) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        Self::at_expected_reconcile_states(key, state)(s)
        ==> {
            Self::has_pending_req_msg(s, key)
            && Self::request_sent_by_controller(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
            && (s.in_flight().contains(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
            || exists |resp_msg: MsgType<E>| {
                #[trigger] s.in_flight().contains(resp_msg)
                && Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
            })
        }
    }
}

pub open spec fn no_pending_req_msg_at_reconcile_state(
    key: ObjectRef, state: spec_fn(R::T) -> bool
) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        Self::at_expected_reconcile_states(key, state)(s)
        ==> Self::no_pending_req_msg(s, key)
    }
}

pub open spec fn resp_in_flight_matches_pending_req_at_reconcile_state(
    key: ObjectRef, state: spec_fn(R::T) -> bool
) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        Self::at_expected_reconcile_states(key, state)(s)
        && Self::has_pending_req_msg(s, key)
        && Self::request_sent_by_controller(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
        && exists |resp_msg: MsgType<E>| {
            #[trigger] s.in_flight().contains(resp_msg)
            && Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
        }
    }
}

}

}
