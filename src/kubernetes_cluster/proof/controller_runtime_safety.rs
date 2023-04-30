// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_cluster::{
    proof::{kubernetes_api_safety, wf1_assistant::controller_action_pre_implies_next_pre},
    spec::{
        controller::common::{ControllerAction, ControllerActionInput},
        controller::state_machine::controller,
        distributed_system::*,
        message::*,
    },
};
use crate::reconciler::spec::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use builtin::*;
use builtin_macros::*;
use vstd::{option::*, result::*};

verus! {

pub open spec fn pending_msg_is_req_msg<T>() -> StatePred<State<T>> {
    |s: State<T>| {
        forall |cr_key: ObjectRef|
            #[trigger] s.reconcile_state_contains(cr_key)
            && s.reconcile_state_of(cr_key).pending_req_msg.is_Some()
            ==> s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0().content.is_APIRequest()
    }
}

pub open spec fn pending_req_has_unique_id<T>(cr_key: ObjectRef) -> StatePred<State<T>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<T>| {
        s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).pending_req_msg.is_Some()
        ==> (
            forall |other_key: ObjectRef|
                #[trigger] s.reconcile_state_contains(other_key)
                && s.reconcile_state_of(other_key).pending_req_msg.is_Some()
                && other_key !== cr_key
                ==> s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0().content.get_req_id() !== s.reconcile_state_of(other_key).pending_req_msg.get_Some_0().content.get_req_id()
            )
    }
}

pub open spec fn pending_req_has_lower_req_id<T>() -> StatePred<State<T>> {
    |s: State<T>| {
        forall |cr_key: ObjectRef|
            #[trigger] s.reconcile_state_contains(cr_key)
            && s.reconcile_state_of(cr_key).pending_req_msg.is_Some()
            ==> s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0().content.get_req_id() < s.chan_manager.cur_chan_id
    }
}

pub proof fn lemma_always_pending_req_has_lower_req_id<T>(reconciler: Reconciler<T>)
    ensures
        sm_spec(reconciler).entails(always(lift_state(pending_req_has_lower_req_id()))),
{
    let invariant = pending_req_has_lower_req_id::<T>();
    init_invariant::<State<T>>(sm_spec(reconciler), init(reconciler), next(reconciler), invariant);
}

pub open spec fn resp_matches_at_most_one_pending_req<T>(resp_msg: Message, cr_key: ObjectRef) -> StatePred<State<T>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<T>| {
        s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).pending_req_msg.is_Some()
        && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
        ==> (
            forall |other_key: ObjectRef|
                #[trigger] s.reconcile_state_contains(other_key)
                && s.reconcile_state_of(other_key).pending_req_msg.is_Some()
                && other_key !== cr_key
                ==> !resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(other_key).pending_req_msg.get_Some_0())
            )
    }
}

pub proof fn lemma_always_resp_matches_at_most_one_pending_req<T>(reconciler: Reconciler<T>, resp_msg: Message, cr_key: ObjectRef)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(reconciler).entails(always(lift_state(resp_matches_at_most_one_pending_req(resp_msg, cr_key)))),
{
    let invariant = resp_matches_at_most_one_pending_req::<T>(resp_msg, cr_key);
    let stronger_next = |s, s_prime: State<T>| {
        &&& next(reconciler)(s, s_prime)
        &&& pending_req_has_lower_req_id()(s)
    };

    lemma_always_pending_req_has_lower_req_id::<T>(reconciler);

    strengthen_next::<State<T>>(sm_spec(reconciler), next(reconciler), pending_req_has_lower_req_id(), stronger_next);
    init_invariant::<State<T>>(sm_spec(reconciler), init(reconciler), stronger_next, invariant);
}

pub proof fn lemma_always_forall_resp_matches_at_most_one_pending_req<T>(reconciler: Reconciler<T>, cr_key: ObjectRef)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(reconciler).entails(tla_forall(|msg| always(lift_state(resp_matches_at_most_one_pending_req(msg, cr_key))))),
{
    let m_to_p = |msg| always(lift_state(resp_matches_at_most_one_pending_req(msg, cr_key)));
    assert forall |msg| #[trigger] sm_spec(reconciler).entails(m_to_p(msg)) by {
        lemma_always_resp_matches_at_most_one_pending_req::<T>(reconciler, msg, cr_key);
    };
    spec_entails_tla_forall(sm_spec(reconciler), m_to_p);
}

pub open spec fn each_resp_matches_at_most_one_pending_req<T>(cr_key: ObjectRef) -> StatePred<State<T>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<T>| {
        forall |resp_msg: Message|
            s.reconcile_state_contains(cr_key)
            && s.reconcile_state_of(cr_key).pending_req_msg.is_Some()
            && #[trigger] resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
            ==> (
                forall |other_key: ObjectRef|
                    #[trigger] s.reconcile_state_contains(other_key)
                    && s.reconcile_state_of(other_key).pending_req_msg.is_Some()
                    && other_key !== cr_key
                    ==> !resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(other_key).pending_req_msg.get_Some_0())
                )
    }
}

pub proof fn lemma_always_each_resp_matches_at_most_one_pending_req<T>(reconciler: Reconciler<T>, cr_key: ObjectRef)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(reconciler).entails(always(lift_state(each_resp_matches_at_most_one_pending_req(cr_key)))),
{
    let invariant = each_resp_matches_at_most_one_pending_req::<T>(cr_key);
    let stronger_next = |s, s_prime: State<T>| {
        &&& next(reconciler)(s, s_prime)
        &&& pending_req_has_lower_req_id()(s)
    };

    lemma_always_pending_req_has_lower_req_id::<T>(reconciler);

    strengthen_next::<State<T>>(sm_spec(reconciler), next(reconciler), pending_req_has_lower_req_id(), stronger_next);
    init_invariant::<State<T>>(sm_spec(reconciler), init(reconciler), stronger_next, invariant);
}

}
