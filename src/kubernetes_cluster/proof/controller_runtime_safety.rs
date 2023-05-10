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

pub open spec fn every_in_flight_msg_has_lower_id_than_chan_manager<T>() -> StatePred<State<T>> {
    |s: State<T>| {
        forall |msg: Message|
            #[trigger] s.message_in_flight(msg)
            ==> msg.content.get_msg_id() < s.chan_manager.cur_chan_id
    }
}

pub proof fn lemma_always_every_in_flight_msg_has_lower_id_than_chan_manager<T>(reconciler: Reconciler<T>)
    ensures
        sm_spec(reconciler).entails(always(lift_state(every_in_flight_msg_has_lower_id_than_chan_manager()))),
{
    let invariant = every_in_flight_msg_has_lower_id_than_chan_manager::<T>();
    assert forall |s, s_prime: State<T>| invariant(s) && #[trigger] next(reconciler)(s, s_prime) implies invariant(s_prime) by {
        assert forall |msg: Message| #[trigger] s_prime.message_in_flight(msg) implies msg.content.get_msg_id() < s_prime.chan_manager.cur_chan_id by {
            assert(s.chan_manager.cur_chan_id <= s_prime.chan_manager.cur_chan_id);
            if (s.message_in_flight(msg)) {
                assert(msg.content.get_msg_id() < s.chan_manager.cur_chan_id);
                assert(msg.content.get_msg_id() < s_prime.chan_manager.cur_chan_id);
            } else {
                match msg.content {
                    MessageContent::APIRequest(_, _) => assert(s.chan_manager.cur_chan_id < s_prime.chan_manager.cur_chan_id),
                    MessageContent::APIResponse(_, id) => {
                        let next_step = choose |step: Step| next_step(reconciler, s, s_prime, step);
                        let input = next_step.get_KubernetesAPIStep_0();
                        assert(s.message_in_flight(input.get_Some_0()));
                        assert(id == input.get_Some_0().content.get_req_id());
                        assert(input.get_Some_0().content.get_req_id() < s.chan_manager.cur_chan_id);
                    }
                }
                
            }
        };
    };
    init_invariant::<State<T>>(sm_spec(reconciler), init(reconciler), next(reconciler), invariant);
}

pub open spec fn every_in_flight_req_is_unique<T>() -> StatePred<State<T>> {
    |s: State<T>| {
        forall |msg: Message|
            msg.content.is_APIRequest() && #[trigger] s.message_in_flight(msg)
            ==> s.network_state.in_flight.count(msg) == 1
    }
}

pub proof fn lemma_always_every_in_flight_req_is_unique<T>(reconciler: Reconciler<T>)
    ensures
        sm_spec(reconciler).entails(
            always(lift_state(every_in_flight_req_is_unique::<T>()))
        ),
{
    let invariant = every_in_flight_req_is_unique::<T>();
    let stronger_next = |s, s_prime: State<T>| {
        &&& next(reconciler)(s, s_prime)
        &&& every_in_flight_msg_has_lower_id_than_chan_manager()(s)
    };
    lemma_always_every_in_flight_msg_has_lower_id_than_chan_manager::<T>(reconciler);
    strengthen_next::<State<T>>(sm_spec(reconciler), next(reconciler), every_in_flight_msg_has_lower_id_than_chan_manager(), stronger_next);
    assert forall |s, s_prime: State<T>| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        assert forall |msg: Message| msg.content.is_APIRequest() && #[trigger] s_prime.message_in_flight(msg) implies s_prime.network_state.in_flight.count(msg) == 1 by {
            if (s.message_in_flight(msg)) {
                assert(s.network_state.in_flight.count(msg) == 1);
            }
        };
    };
    init_invariant::<State<T>>(sm_spec(reconciler), init(reconciler), stronger_next, invariant);
}

pub open spec fn every_in_flight_msg_has_unique_id<T>() -> StatePred<State<T>> {
    |s: State<T>| {
        forall |msg: Message|
            #[trigger] s.message_in_flight(msg)
            ==> (
                forall |other_msg: Message|
                    #[trigger] s.message_in_flight(other_msg)
                    && msg != other_msg
                    ==> msg.content.get_msg_id() != other_msg.content.get_msg_id()
            )
    }
}

pub proof fn lemma_always_every_in_flight_msg_has_unique_id<T>(reconciler: Reconciler<T>)
    ensures
        sm_spec(reconciler).entails(
            always(lift_state(every_in_flight_msg_has_unique_id::<T>()))
        ),
{
    let invariant = every_in_flight_msg_has_unique_id::<T>();
    let stronger_next = |s, s_prime: State<T>| {
        next(reconciler)(s, s_prime)
        && every_in_flight_msg_has_lower_id_than_chan_manager::<T>()(s)
        && every_in_flight_req_is_unique::<T>()(s)
    };
    lemma_always_every_in_flight_msg_has_lower_id_than_chan_manager::<T>(reconciler);
    lemma_always_every_in_flight_req_is_unique::<T>(reconciler);
    strengthen_next_2::<State<T>>(sm_spec(reconciler), next(reconciler), every_in_flight_msg_has_lower_id_than_chan_manager::<T>(), every_in_flight_req_is_unique::<T>(), stronger_next);
    assert forall |s, s_prime: State<T>| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        next_and_unique_lower_msg_id_preserves_in_flight_msg_has_unique_id::<T>(reconciler, s, s_prime);
    };
    init_invariant::<State<T>>(sm_spec(reconciler), init(reconciler), stronger_next, invariant);
}

proof fn next_and_unique_lower_msg_id_preserves_in_flight_msg_has_unique_id<T>(reconciler: Reconciler<T>, s: State<T>, s_prime: State<T>)
    requires
        next(reconciler)(s, s_prime), 
        every_in_flight_msg_has_lower_id_than_chan_manager::<T>()(s),every_in_flight_req_is_unique::<T>()(s), every_in_flight_msg_has_unique_id::<T>()(s), // the invariant
    ensures
        every_in_flight_msg_has_unique_id::<T>()(s_prime),
{
    assert forall |msg: Message| #[trigger] s_prime.message_in_flight(msg) implies (forall |other_msg: Message| #[trigger] s_prime.message_in_flight(other_msg) && msg != other_msg ==> msg.content.get_msg_id() != other_msg.content.get_msg_id()) by {
        assert forall |other_msg: Message| #[trigger] s_prime.message_in_flight(other_msg) && msg != other_msg implies msg.content.get_msg_id() != other_msg.content.get_msg_id() by {
            // At most one message will be added to the network_state.in_flight for each action.
            assert(s.message_in_flight(msg) || s.message_in_flight(other_msg));
            if (s.message_in_flight(msg) && s.message_in_flight(other_msg)) {
                assert(msg.content.get_msg_id() != other_msg.content.get_msg_id());
            } else {
                if (s.message_in_flight(msg)) {
                    newly_added_msg_have_different_id_from_existing_ones(reconciler, s, s_prime, msg, other_msg);
                } else {
                    newly_added_msg_have_different_id_from_existing_ones(reconciler, s, s_prime, other_msg, msg);
                }
            }
        }
    };
}

proof fn newly_added_msg_have_different_id_from_existing_ones<T>(reconciler: Reconciler<T>, s: State<T>, s_prime: State<T>, msg_1: Message, msg_2: Message)
    requires
        next(reconciler)(s, s_prime), 
        every_in_flight_msg_has_lower_id_than_chan_manager::<T>()(s), every_in_flight_req_is_unique::<T>()(s), 
        s.message_in_flight(msg_1), !s.message_in_flight(msg_2), 
        s_prime.message_in_flight(msg_1), s_prime.message_in_flight(msg_2),
        every_in_flight_msg_has_unique_id::<T>()(s), // the invariant
    ensures
        msg_1.content.get_msg_id() != msg_2.content.get_msg_id(),
{
    if (msg_2.content.is_APIResponse()) {
        let next_step = choose |step: Step| next_step(reconciler, s, s_prime, step);
        let input = next_step.get_KubernetesAPIStep_0();
        assert(s.network_state.in_flight.count(input.get_Some_0()) <= 1);
        assert(msg_1.content.get_msg_id() != msg_2.content.get_msg_id());
    }
}

pub open spec fn every_in_flight_req_has_unique_id<T>() -> StatePred<State<T>> {
    |s: State<T>| {
        forall |req_msg: Message| 
            #[trigger] s.message_in_flight(req_msg)
            && req_msg.content.is_APIRequest()
            ==> (
                forall |other_msg: Message|
                    #[trigger] s.message_in_flight(other_msg)
                    && other_msg.content.is_APIRequest()
                    && req_msg != other_msg
                    ==> req_msg.content.get_req_id() != other_msg.content.get_req_id()
                )
    }
}

pub proof fn lemma_always_every_in_flight_req_has_unique_id<T>(reconciler: Reconciler<T>)
    ensures
        sm_spec(reconciler).entails(
            always(lift_state(every_in_flight_req_has_unique_id::<T>()))
        ),
{
    let invariant = every_in_flight_req_has_unique_id::<T>();
    let stronger_next = |s, s_prime: State<T>| {
        next(reconciler)(s, s_prime)
        && every_in_flight_msg_has_lower_id_than_chan_manager::<T>()(s)
    };
    lemma_always_every_in_flight_msg_has_lower_id_than_chan_manager::<T>(reconciler);
    strengthen_next::<State<T>>(sm_spec(reconciler), next(reconciler), every_in_flight_msg_has_lower_id_than_chan_manager::<T>(), stronger_next);
    assert forall |s, s_prime: State<T>| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        assert forall |req_msg: Message| #[trigger] s_prime.message_in_flight(req_msg) && req_msg.content.is_APIRequest() implies (
            forall |other_msg: Message| #[trigger] s_prime.message_in_flight(other_msg) && other_msg.content.is_APIRequest() && req_msg != other_msg ==> req_msg.content.get_req_id() != other_msg.content.get_req_id()) by {
                assert forall |other_msg: Message| #[trigger] s_prime.message_in_flight(other_msg) && other_msg.content.is_APIRequest() && req_msg != other_msg implies req_msg.content.get_req_id() != other_msg.content.get_req_id() by {
                    // At most one request will be added to the network_state.in_flight for each action.
                    assert(s.message_in_flight(req_msg) || s.message_in_flight(other_msg));
                    if (s.message_in_flight(req_msg) && s.message_in_flight(other_msg)) {
                        assert(req_msg.content.get_req_id() != other_msg.content.get_req_id());
                    }
                }
            };
    };
    init_invariant::<State<T>>(sm_spec(reconciler), init(reconciler), stronger_next, invariant);
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

pub open spec fn at_most_one_resp_matches_req<T>(resp_msg: Message, cr_key: ObjectRef) -> StatePred<State<T>>
{
    |s: State<T>| {
        s.reconcile_state_contains(cr_key)
        && s.message_in_flight(resp_msg)
        && s.reconcile_state_of(cr_key).pending_req_msg.is_Some()
        && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
        ==> (
            forall |other_resp: Message| other_resp != resp_msg && #[trigger] s.message_in_flight(other_resp)
            ==> !resp_msg_matches_req_msg(other_resp, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
        )
    }
}

pub proof fn lemma_always_at_most_one_resp_matches_req<T>(reconciler: Reconciler<T>, resp_msg: Message, cr_key: ObjectRef)
    ensures
        sm_spec(reconciler).entails(always(lift_state(at_most_one_resp_matches_req(resp_msg, cr_key)))),
{
    implies_preserved_by_always::<State<T>>(every_in_flight_msg_has_unique_id::<T>(), at_most_one_resp_matches_req::<T>(resp_msg, cr_key));
    lemma_always_every_in_flight_msg_has_unique_id::<T>(reconciler);
    entails_trans::<State<T>>(sm_spec(reconciler), always(lift_state(every_in_flight_msg_has_unique_id::<T>())), always(lift_state(at_most_one_resp_matches_req::<T>(resp_msg, cr_key))));
}

pub proof fn lemma_forall_always_at_most_one_resp_matches_req<T>(reconciler: Reconciler<T>, cr_key: ObjectRef)
    ensures
        sm_spec(reconciler).entails(tla_forall(|resp_msg: Message| always(lift_state(at_most_one_resp_matches_req(resp_msg, cr_key))))),
{
    let m_to_p = |msg| always(lift_state(at_most_one_resp_matches_req(msg, cr_key)));
    assert forall |msg| #[trigger] sm_spec(reconciler).entails(m_to_p(msg)) by {
        lemma_always_at_most_one_resp_matches_req::<T>(reconciler, msg, cr_key);
    }
    spec_entails_tla_forall(sm_spec(reconciler), m_to_p);
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

pub proof fn lemma_forall_resp_always_matches_at_most_one_pending_req<T>(reconciler: Reconciler<T>, cr_key: ObjectRef)
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
