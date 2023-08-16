// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::{api_method::*, common::*, error::*, resource::*};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerAction, ControllerActionInput},
    message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn every_in_flight_msg_has_lower_id_than_allocator() -> StatePred<Self> {
    |s: Self| {
        forall |msg: Message|
            #[trigger] s.message_in_flight(msg)
            ==> msg.content.get_rest_id() < s.rest_id_allocator.rest_id_counter
    }
}

pub proof fn lemma_always_every_in_flight_msg_has_lower_id_than_allocator
    ()
    ensures
        Self::sm_spec().entails(always(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()))),
{
    let invariant = Self::every_in_flight_msg_has_lower_id_than_allocator();
    assert forall |s, s_prime: Self| invariant(s) && #[trigger] Self::next()(s, s_prime) implies
    invariant(s_prime) by {
        Self::next_preserves_every_in_flight_msg_has_lower_id_than_allocator(s, s_prime);
    };
    init_invariant::<Self>(Self::sm_spec(), Self::init(), Self::next(), invariant);
}

proof fn next_preserves_every_in_flight_msg_has_lower_id_than_allocator(
    s: Self, s_prime: Self
)
    requires
        Self::every_in_flight_msg_has_lower_id_than_allocator()(s), Self::next()(s, s_prime),
    ensures
        Self::every_in_flight_msg_has_lower_id_than_allocator()(s_prime),
{
    assert forall |msg: Message| #[trigger] s_prime.message_in_flight(msg) implies
    msg.content.get_rest_id() < s_prime.rest_id_allocator.rest_id_counter by {
        assert(s.rest_id_allocator.rest_id_counter <= s_prime.rest_id_allocator.rest_id_counter);
        if (s.message_in_flight(msg)) {
            assert(msg.content.get_rest_id() < s.rest_id_allocator.rest_id_counter);
        } else {
            match msg.content {
                MessageContent::APIRequest(_, _) => assert(s.rest_id_allocator.rest_id_counter < s_prime.rest_id_allocator.rest_id_counter),
                MessageContent::APIResponse(_, id) => {
                    let next_step = choose |step: Step<K, E>| Self::next_step(s, s_prime, step);
                    match next_step {
                        Step::KubernetesAPIStep(input) => {
                            let req_msg = input.get_Some_0();
                            assert(s.message_in_flight(req_msg));
                            assert(id == req_msg.content.get_req_id());
                        }
                        Step::KubernetesBusy(input) => {
                            let req_msg = input.get_Some_0();
                            assert(s.message_in_flight(req_msg));
                            assert(id == req_msg.content.get_req_id());
                        }
                        _ => assert(false),
                    }
                }
            }
        }
    };
}

pub open spec fn every_in_flight_req_is_unique() -> StatePred<Self> {
    |s: Self| {
        forall |msg: Message|
            msg.content.is_APIRequest() && #[trigger] s.message_in_flight(msg)
            ==> s.network_state.in_flight.count(msg) == 1
    }
}

pub proof fn lemma_always_every_in_flight_req_is_unique()
    ensures
        Self::sm_spec().entails(
            always(lift_state(Self::every_in_flight_req_is_unique()))
        ),
{
    let invariant = Self::every_in_flight_req_is_unique();
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
    };
    Self::lemma_always_every_in_flight_msg_has_lower_id_than_allocator();
    strengthen_next::<Self>(
        Self::sm_spec(), Self::next(), Self::every_in_flight_msg_has_lower_id_than_allocator(), stronger_next
    );
    assert forall |s, s_prime: Self| invariant(s) && #[trigger] stronger_next(s, s_prime) implies
    invariant(s_prime) by {
        assert forall |msg: Message| msg.content.is_APIRequest() && #[trigger] s_prime.message_in_flight(msg) implies
        s_prime.network_state.in_flight.count(msg) == 1 by {
            if (s.message_in_flight(msg)) {
                assert(s.network_state.in_flight.count(msg) == 1);
            }
        };
    };
    init_invariant::<Self>(Self::sm_spec(), Self::init(), stronger_next, invariant);
}

pub open spec fn every_in_flight_msg_has_unique_id() -> StatePred<Self> {
    |s: Self| {
        forall |msg: Message|
            #[trigger] s.message_in_flight(msg)
            ==> (
                forall |other_msg: Message|
                    #[trigger] s.message_in_flight(other_msg)
                    && msg != other_msg
                    ==> msg.content.get_rest_id() != other_msg.content.get_rest_id()
            )
    }
}

pub proof fn lemma_always_every_in_flight_msg_has_unique_id()
    ensures
        Self::sm_spec().entails(
            always(lift_state(Self::every_in_flight_msg_has_unique_id()))
        ),
{
    let invariant = Self::every_in_flight_msg_has_unique_id();
    let stronger_next = |s, s_prime: Self| {
        Self::next()(s, s_prime)
        && Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
        && Self::every_in_flight_req_is_unique()(s)
    };
    Self::lemma_always_every_in_flight_msg_has_lower_id_than_allocator();
    Self::lemma_always_every_in_flight_req_is_unique();
    strengthen_next_n!(
        stronger_next, Self::sm_spec(),
        lift_action(Self::next()),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Self::every_in_flight_req_is_unique())
    );
    assert forall |s, s_prime: Self| invariant(s) && #[trigger] stronger_next(s, s_prime) implies
    invariant(s_prime) by {
        Self::next_and_unique_lower_msg_id_preserves_in_flight_msg_has_unique_id(s, s_prime);
    };
    init_invariant::<Self>(Self::sm_spec(), Self::init(), stronger_next, invariant);
}

proof fn next_and_unique_lower_msg_id_preserves_in_flight_msg_has_unique_id(
    s: Self, s_prime: Self
)
    requires
        Self::next()(s, s_prime),
        Self::every_in_flight_msg_has_lower_id_than_allocator()(s),
        Self::every_in_flight_req_is_unique()(s),
        Self::every_in_flight_msg_has_unique_id()(s), // the invariant
    ensures
        Self::every_in_flight_msg_has_unique_id()(s_prime),
{
    assert forall |msg: Message| #[trigger] s_prime.message_in_flight(msg) implies
    (forall |other_msg: Message| #[trigger] s_prime.message_in_flight(other_msg) && msg != other_msg
        ==> msg.content.get_rest_id() != other_msg.content.get_rest_id()) by {
        assert forall |other_msg: Message| #[trigger] s_prime.message_in_flight(other_msg) && msg != other_msg implies
        msg.content.get_rest_id() != other_msg.content.get_rest_id() by {
            // At most one message will be added to the network_state.in_flight for each action.
            assert(s.message_in_flight(msg) || s.message_in_flight(other_msg));
            if (s.message_in_flight(msg) && s.message_in_flight(other_msg)) {
                assert(msg.content.get_rest_id() != other_msg.content.get_rest_id());
            } else {
                if (s.message_in_flight(msg)) {
                    Self::newly_added_msg_have_different_id_from_existing_ones(s, s_prime, msg, other_msg);
                } else {
                    Self::newly_added_msg_have_different_id_from_existing_ones(s, s_prime, other_msg, msg);
                }
            }
        }
    };
}

proof fn newly_added_msg_have_different_id_from_existing_ones(
    s: Self, s_prime: Self, msg_1: Message, msg_2: Message
)
    requires
        Self::next()(s, s_prime),
        Self::every_in_flight_msg_has_lower_id_than_allocator()(s),
        Self::every_in_flight_req_is_unique()(s),
        s.message_in_flight(msg_1),
        !s.message_in_flight(msg_2),
        s_prime.message_in_flight(msg_1),
        s_prime.message_in_flight(msg_2),
        Self::every_in_flight_msg_has_unique_id()(s), // the invariant
    ensures
        msg_1.content.get_rest_id() != msg_2.content.get_rest_id(),
{
    if (msg_2.content.is_APIResponse()) {
        let next_step = choose |step: Step<K, E>| Self::next_step(s, s_prime, step);
        match next_step {
            Step::KubernetesAPIStep(input) => {
                let req_msg = input.get_Some_0();
                assert(s.network_state.in_flight.count(req_msg) <= 1);
                assert(msg_1.content.get_rest_id() != msg_2.content.get_rest_id());
            }
            Step::KubernetesBusy(input) => {
                let req_msg = input.get_Some_0();
                assert(s.network_state.in_flight.count(req_msg) <= 1);
                assert(msg_1.content.get_rest_id() != msg_2.content.get_rest_id());
            }
            _ => assert(false),
        }
    }
}

pub open spec fn req_in_flight_or_pending_at_controller(req_msg: Message, s: Self) -> bool {
    req_msg.content.is_APIRequest() && (s.message_in_flight(req_msg)
    || exists |cr_key: ObjectRef| (
        #[trigger] s.reconcile_state_contains(cr_key)
        && Self::pending_k8s_api_req_msg_is(s, cr_key, req_msg)
        && s.reconcile_state_of(cr_key).pending_external_api_input.is_None()
    ))
}

pub open spec fn pending_req_has_lower_req_id_than_allocator() -> StatePred<Self> {
    |s: Self| {
        forall |cr_key: ObjectRef|
            #[trigger] s.reconcile_state_contains(cr_key)
            && Self::pending_k8s_api_req_msg(s, cr_key)
            ==> s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0().content.get_req_id() < s.rest_id_allocator.rest_id_counter
    }
}

pub proof fn lemma_always_pending_req_has_lower_req_id_than_allocator()
    ensures
        Self::sm_spec().entails(always(lift_state(Self::pending_req_has_lower_req_id_than_allocator()))),
{
    let invariant = Self::pending_req_has_lower_req_id_than_allocator();
    init_invariant::<Self>(
        Self::sm_spec(), Self::init(), Self::next(), invariant
    );
}

}

}
